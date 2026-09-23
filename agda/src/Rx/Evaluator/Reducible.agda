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

-- THE ONE CHANGE THIS MODULE IS BUILT AROUND: A SUBSCRIBE TAKES THE
-- REST OF THE PATH IN, AS AN OPAQUE CONTINUATION, AND ANSWERS AT THE
-- ROOT.  The candidate used to hand its emissions UP at the source's
-- element type, beside a satisfaction column, for whoever consumed the
-- subscribe to push through its frame -- and whichever way that answer
-- was carried, a value delivered during the subscribe by a share's
-- fan-out arrived either behind it or ahead of it, and a counting
-- frame could tell.  Folding where a value is produced is the only
-- order that agrees with rxjs, and the recorded route to it died on
-- the candidate's type: a root-typed answer has no source type in it,
-- so a satisfaction column over the answer ranges over the root type
-- and the Girard-Tait descent has nothing to fall on.
--
-- The repair is to put the descent on the CONTINUATION's parameter
-- instead of on the answer.  `RP m (Red m u) S κ` is the path above
-- the subscribe, packaged as a fold that takes values AT `u` with
-- their candidates and answers at the root; the candidate at `obs u`
-- takes one in and hands its state back.  `Red m u` occurs in the
-- observable arm only as that parameter, so the recursion on `Ty` is
-- exactly as structural as before -- and the answer is at `t`,
-- because the answer carries no candidate at all any more.  The
-- satisfaction column is gone: candidates travel DOWN, into the
-- continuation, never up with the result.

-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- takes the scheduler and the evaluator state as plain indices with no
-- precondition, so the candidate can demand subscribability in EVERY
-- state whose room is under the ceiling -- which is what lets a
-- flattener's hop subscribe its inner in whatever state the outer
-- delivery reached, with no invariant threaded.

-- AND THE CEILING IS AN INDEX OF THE CANDIDATE, WHICH AN ANSWER
-- CARRYING CANDIDATES COULD NOT AFFORD.  It could not be done while the
-- answer carried candidates: a def subscribed at the connect's lower
-- ceiling came back proven at that ceiling and the arm owed them at
-- the outer, and the predicate grows with the ceiling, so no weakening
-- closed it.  Here nothing ever comes back.  A candidate proven at a
-- lower ceiling is only ever APPLIED, to a continuation that has been
-- dropped to that ceiling by forgetting what it was going to be
-- handed; the outer arm sees a state and an answer, and states carry
-- no ceiling.  That is the whole reason the index is admissible now,
-- and it is what lets a connect's peel fund the raw fan-out below it.

-- AND THE ENVIRONMENT IS CARRIED RATHER THAN SUBSTITUTED, WHICH IS
-- WHAT MAKES THE WHOLE SUBSTITUTION LAYER UNNECESSARY.  An observable
-- value IS a body paired with the environment it closed over, so the
-- expression face concludes about that pair directly and no lemma
-- relating a peel to a substitution is owed anywhere.
module Rx.Evaluator.Reducible where

open import Data.Bool using (Bool; true; false; if_then_else_; T; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_; map; length; null)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _∸_; s≤s; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; _≟_; ≮⇒≥; ≤-refl; ≤-trans; <⇒≤; m≤n+m; m≤m+n; <ᵇ⇒<; ∸-monoʳ-<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Tick; hot; cold)
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
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ; ib-topᵗ)
open import Rx.Mint using (nodeᵏ; regᵏ; sourceᵏ; ordinalᵏ; freshId; setAt)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; _↠[_]_; map-f; take-f; scan-f; batchSync-f; from-inner;
  thru-outer; share-sink; root; mergeAllᵒ; switchᵒ; exhaustᵒ; AllOp; NodeId; NodeState;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st; takeVals; takeDispatch;
  scanVals; scanDispatch; batchVals; batchDispatch; batchBuf; lookupNode; setNode; installNode;
  memberSource; consumeUsable; hasRoom; drainSt; switchKill; register; atSlot; atDyn; resolve;
  lowerFloor; aliveThroughᶠ; shareAdmit; shareDying; shareSpend; thruWrap; RegId)
open import Rx.Exp.ValEq using (eqVal)
open import Rx.Evaluator.Unconn-Arith using (unconn; unconn-insert; room-keeps; keeps-refl)
open import Rx.Evaluator.Keeps using (switchKill-keeps; subscribeE-keeps; subscribeInner-keeps; scanDispatch-keeps;
  takeDispatch-keeps; batchDispatch-keeps; thruWrap-keeps; thruConsume-keeps; thruWalk-keeps;
  innerReact-keeps; foldPath-keeps; shareDying-keeps; shareSpend-keeps; shareGo-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; step-map; step-scan; step-take; step-batchSync; step-from-inner; subs-of;
  subs-empty; subs-map; subs-take-zero; subs-take-suc; subs-scan; subs-batchSync; subs-mint;
  subs-defer; subs-floor; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async;
  subs-μ; sub-all; subs-merge-all; subs-switch-all; subs-exhaust-all; thruConsume⇓; thruWalk⇓;
  step-thru-outer; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; walk-nil;
  walk-cons; walk-end; walk-more; subs-shared; slot-spent; slot-join; slot-connect; connect;
  subscribeInner⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; foldPath⇓; dispatchShare⇓;
  shareWalk⇓; shareGo⇓; drain-spent; drain-nil; drain-no-room; drain-room; finish-all-drain;
  finish-switch-clear; finish-exhaust-clear; finish-nil; react-false; react-alive; react-dead;
  fold-root; fold-sink; fold-step; disp; go-nil; go-cut; go-live)

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

-- THE CONTINUATION: THE REST OF THE PATH, AS A FOLD THAT TAKES
-- CANDIDATES AND ANSWERS AT THE ROOT.  A subscribe never sees the
-- frames above it; it sees one function that takes a burst at its own
-- element type, a candidate column over that burst, the completion
-- flag, and a state under the ceiling, and hands back the root-typed
-- stream the fold produced, the state after it, the derivation, and
-- the continuation's own updated state.
--
-- THE STATE TYPE IS EXPLICIT SO THAT A FRAME CAN GROW IT AND ITS
-- SUBSCRIBE ARM CAN READ IT BACK.  A frame continuation over a parent
-- at state `S` is a continuation at state `FrameSt × S`: the frame's
-- own held candidates in front, the parent's state behind.  The arm
-- that pushed the frame calls the sub-subscribe with that pair and
-- gets the pair back -- which is what the bracket's flush and the
-- fold's cell need, and what an opaque closure could not have handed
-- out.  A continuation at a fixed state would have had to be returned
-- afresh from every fold, and a frame's state would then have been
-- hidden inside a value the arm cannot open.
--
-- THE CANDIDATE COLUMN IS `Maybe`, AND `nothing` IS A VALUE THE
-- CONTINUATION CANNOT VOUCH FOR.  Every value arriving through a live
-- subscribe has a candidate; a value written into a store by a fold
-- the continuation never saw, and read back, has none.  A `nothing`
-- arriving where a candidate is NEEDED -- a flattener about to
-- subscribe it -- is answered by the runtime guard at `red-consume`,
-- and nowhere else is a candidate needed at all: every other frame
-- either passes values through or transforms them by a closure the
-- term face already proved.
record RP {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
          (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t) : Set₁ where
  constructor mkRP
  field
    fold : S → (now : Tick) (vals : List (Val Γ u)) → All (λ v → Maybe (P v)) vals
         → (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
         → Σ (Stream Γ t × Sched Γ × EvalSt e)
             (λ r → foldPath⇓ {e = e} now κ vals fin sched st r)
           × S
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
    × S

-- A MAPPING FRAME APPLIES ITS CLOSURE TO EVERY ARRIVING VALUE, so what
-- it produces is reducible exactly when the closure sends reducible to
-- reducible.  That is the only thing a frame wants from the term face.
RedFn : ∀ {n} {Γ : Ctx n} (m : ℕ) {s u} → FnClo Γ s u → Set₁
RedFn {Γ = Γ} m {s = s} {u = u} fn =
  ∀ {v : Val Γ s} → Red m s v → Red m u (applyClo fn v)

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's closure pairs a term with one
-- such environment, so the fundamental theorem at terms has to be
-- stated under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} (m : ℕ) {Θ : List Ty} → Env Γ Θ → Set₁
RedEnv m []ᵉ                  = ⊤
RedEnv m (_∷ᵉ_ {s = t} v vs)  = Red m t v × RedEnv m vs

------------------------------------------------------------------
-- CANDIDATES ACROSS THE FRAMES THAT CARRY NO STORE PAYLOAD.
------------------------------------------------------------------

-- EVERY VALUE OF A DATA TYPE IS REDUCIBLE, AND THAT IS WHY THE SLOT
-- ARM IS SHORT.  The candidate is trivial at each data former and
-- uninhabitable at `obs`, so the recursion here is the same one `Red`
-- itself runs -- it just has to be SAID, because a slot's element type
-- is `lookup Γ i` and no reduction fires on a neutral index.  What
-- carries it is the side condition every scripted slot already holds.
-- THE PRODUCT AND SUM ARMS OF `isData` GUARD ON THE LEFT FACTOR, so
-- the witness has to be taken apart before either side can be used.
T-if : ∀ (b c : Bool) → T (if b then c else false) → T b × T c
T-if true  c ok = tt₀ , ok
T-if false c ()

-- The pair descends on the element TYPE, which is an argument of both
-- and shrinks at the one clause that crosses between them.
-- STRUCTURAL SCC: red-data redDatas
red-data : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → T (isData u) → (v : Val Γ u)
         → Red {Γ = Γ} m u v
redDatas : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → T (isData u) → (vs : List (Val Γ u))
         → All (Red {Γ = Γ} m u) vs

red-data m unitᵗ    _  _       = tt
red-data m natᵗ     _  _       = tt
red-data m boolᵗ    _  _       = tt
red-data m uniqᵗ    _  _       = tt
red-data m (listᵗ u) ok vs     = redDatas m u ok vs
red-data m (s ×ᵗ t) ok (a , b) =
  let (o₁ , o₂) = T-if (isData s) (isData t) ok
  in red-data m s o₁ a , red-data m t o₂ b
red-data m (s +ᵗ t) ok (inj₁ a) = red-data m s (proj₁ (T-if (isData s) (isData t) ok)) a
red-data m (s +ᵗ t) ok (inj₂ b) = red-data m t (proj₂ (T-if (isData s) (isData t) ok)) b
red-data m (obs u)  () _

redDatas m u ok []       = []
redDatas m u ok (v ∷ vs) = red-data m u ok v ∷ redDatas m u ok vs

-- A VALUE OF A DATA TYPE NEEDS NO ONE TO VOUCH FOR IT.  Its candidate
-- is `red-data`, which reads nothing but the type, so wherever a
-- column would otherwise leave unvouched -- a registry path's burst, a
-- store read, a dropped continuation -- a data-typed entry is vouched
-- here instead, and only an entry carrying an observable stays blank.
vouch : ∀ {n} {Γ : Ctx n} {m} (u : Ty) (v : Val Γ u) → Maybe (Red m u v)
vouch {m = m} u v with isData u in eq
... | true  = just (red-data m u (subst T (sym eq) tt₀) v)
... | false = nothing

vouchAll : ∀ {n} {Γ : Ctx n} {m} (u : Ty) (vs : List (Val Γ u))
         → All (λ v → Maybe (Red m u v)) vs
vouchAll u []       = []
vouchAll u (v ∷ vs) = vouch u v ∷ vouchAll u vs

-- DROPPING A CONTINUATION TO A LOWER CEILING FORGETS ITS CANDIDATES.
-- A continuation at ceiling `m` folds under any state whose room is
-- at most `m`, so it folds under any state whose room is at most a
-- smaller `m′` -- the witness weakens by transitivity.  What it cannot
-- take is a candidate stated at `m′`: that candidate promises
-- subscribability in FEWER states than the continuation was built to
-- receive.  So the drop hands it none but the data-typed ones, and
-- the lower run reports every other value upward as unvouched-for.  This is the only direction values
-- ever cross a ceiling, and it is the reason the ceiling can be an
-- index at all.
dropRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m m′ u lo}
           {S} {κ : Path Γ lo u t}
       → m′ ≤ m → RP {e = e} m (Red m u) S κ → RP {e = e} m′ (Red m′ u) S κ
fold (dropRP {u = u} le rp) s now vals _ fin sched st rm =
  fold rp s now vals (vouchAll u vals) fin sched st (≤-trans rm le)


-- a column of certainties is a column of candidates
allJust : ∀ {A : Set} {P : A → Set₁} {xs : List A} → All P xs → All (λ x → Maybe (P x)) xs
allJust []       = []
allJust (p ∷ ps) = just p ∷ allJust ps

-- and a column of candidates is a certainty only when every entry is
sequenceAll : ∀ {A : Set} {P : A → Set₁} {xs : List A}
            → All (λ x → Maybe (P x)) xs → Maybe (All P xs)
sequenceAll []               = just []
sequenceAll (nothing ∷ _)    = nothing
sequenceAll (just p ∷ ps) with sequenceAll ps
... | just qs = just (p ∷ qs)
... | nothing = nothing

zipMaybe : ∀ {A B : Set₁} → Maybe A → Maybe B → Maybe (A × B)
zipMaybe (just a) (just b) = just (a , b)
zipMaybe _        _        = nothing

-- THE MAP KEEPS WHAT IT WAS HANDED: a vouched-for value maps to a
-- vouched-for value and an unvouched one stays unvouched.
redMapVals : ∀ {n} {Γ : Ctx n} {m s u} (fn : FnClo Γ s u) → RedFn m fn
           → {vals : List (Val Γ s)} → All (λ v → Maybe (Red m s v)) vals
           → All (λ v → Maybe (Red m u v)) (map (applyClo fn) vals)
redMapVals fn rf []              = []
redMapVals fn rf (just p ∷ ps)   = just (rf p) ∷ redMapVals fn rf ps
redMapVals {s = s} fn rf {v ∷ _} (nothing ∷ ps) =
  mapᵐ rf (vouch s v) ∷ redMapVals fn rf ps

-- A TRUNCATION CANNOT INVENT A VALUE, WHICH IS WHY THE TAKE FRAME NEEDS
-- NOTHING FROM THE STORE.  The node a take installs holds a COUNT, and
-- the dispatch's value column is a prefix of the burst it was handed --
-- on the cut path and the non-cut path alike, and at a stuck lookup the
-- column is empty.  So the arriving candidates are the departing ones
-- and the store decides only HOW MANY survive.
redTakeVals : ∀ {n} {Γ : Ctx n} {s} {P : Val Γ s → Set₁} (k : ℕ)
              {vals : List (Val Γ s)} → All P vals
            → All P (proj₁ (takeVals k vals))
redTakeVals zero          rv        = []
redTakeVals (suc k)       []        = []
redTakeVals (suc zero)    (p ∷ ps)  = p ∷ []
redTakeVals (suc (suc k)) (p ∷ ps)  = p ∷ redTakeVals (suc k) ps

redTakeDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {P : Val Γ s → Set₁}
                  (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
                → All P vals
                → All P (proj₁ (takeDispatch {e = e} nid vals fin sched st ns))
redTakeDispatch nid {vals} fin sched st (just (take-st k)) rv
  with proj₂ (proj₂ (takeVals k vals))
... | true  = redTakeVals k rv
... | false = redTakeVals k rv
redTakeDispatch nid fin sched st (just (cell-st _))           rv = []
redTakeDispatch nid fin sched st (just (batchSync-st _ _ _))  rv = []
redTakeDispatch nid fin sched st (just (mergeAll-st _ _ _ _)) rv = []
redTakeDispatch nid fin sched st (just (switch-st _ _))       rv = []
redTakeDispatch nid fin sched st (just (exhaust-st _ _))      rv = []
redTakeDispatch nid fin sched st nothing                      rv = []

-- THE BRACKET REGROUPS AND INVENTS NOTHING, so a group is vouched for
-- exactly when its head and every member of its tail are.  The
-- product arm of the candidate and its list arm meet here, and both
-- halves come from the one walk that arrived.
redBatchVals : ∀ {n} {Γ : Ctx n} {m s} (sync : Bool)
               {vals : List (Val Γ s)} → All (λ v → Maybe (Red m s v)) vals
             → All (λ v → Maybe (Red m (s ×ᵗ listᵗ s) v)) (batchVals sync vals)
redBatchVals sync  []       = []
redBatchVals true  (p ∷ ps) = zipMaybe p (sequenceAll ps) ∷ []
redBatchVals false (p ∷ ps) = zipMaybe p (just []) ∷ redBatchVals false ps

-- A FOLD IS ITS ACCUMULATOR THREADED ALONG THE BATCH, and so is the
-- claim about it: each output IS the next accumulator, so one walk
-- delivers both the candidate at every emitted value and the candidate
-- at what gets written back.  An unvouched accumulator or an unvouched
-- arrival makes every later output unvouched, because the closure
-- needs both halves of its pair.
redScanVals : ∀ {n} {Γ : Ctx n} {m s u} (fn : FnClo Γ (u ×ᵗ s) u) → RedFn m fn
            → {a : Val Γ u} → Maybe (Red m u a)
            → {vals : List (Val Γ s)} → All (λ v → Maybe (Red m s v)) vals
            → All (λ v → Maybe (Red m u v)) (proj₁ (scanVals fn a vals))
              × Maybe (Red m u (proj₂ (scanVals fn a vals)))
redScanVals fn rf ra []       = [] , ra
redScanVals fn rf ra (p ∷ ps) =
  let step = mapᵐ rf (zipMaybe ra p)
      (qs , last) = redScanVals fn rf step ps
  in step ∷ qs , last

------------------------------------------------------------------
-- THE TWO FRAMES WHOSE STORE HOLDS A VALUE, AND HOW THEIR CANDIDATES
-- SURVIVE A FOLD THE CONTINUATION NEVER SAW.
------------------------------------------------------------------

-- A FOLD'S CELL IS WRITTEN BY TWO KINDS OF FOLD AND READ BY ONE.  The
-- live continuation writes it with candidates in hand; a share's
-- fan-out walks the same frame off the REGISTRY, raw, and writes it
-- behind the continuation's back.  The scan's continuation therefore
-- closes over the accumulator it was built with, together with that
-- value's candidate -- and before it uses the candidate it compares
-- the value it holds against the value the store holds NOW.  Equal,
-- the candidate is a candidate for what the store holds, because the
-- candidate is a property of the value and of nothing else; different,
-- the held candidate says nothing, and the outputs leave unvouched.
--
-- THE HELD CANDIDATE IS CLOSED OVER, NOT THREADED, AND THAT IS A
-- UNIVERSE FACT.  A candidate lives in `Set₁` because its observable
-- arm quantifies over the continuation's state type, so that state
-- type is in `Set` and cannot hold a candidate.  What survives is the
-- candidate the frame was BUILT with: a later fold's accumulator, and
-- every value a bracket buffered, leave unvouched unless their type is
-- data.
--
-- HOLDING THE CANDIDATE AND CERTIFYING IT BY VALUE EQUALITY CALLS
-- NOTHING: a stale cell costs an unvouched column, and an
-- unvouched column costs a guard downstream that the fan-out which
-- staled the cell has already paid for, by dropping the room.
--
-- DEAD ROUTE: re-deriving the cell's candidate by RUNNING it.
--   `red-val` at an observable subscribes the stored closure, so calling
--   it on the cell from inside a fold puts the candidate inside its own
--   recursion at an expression the STORE chose, with the ceiling
--   unchanged -- reading a cell connects nothing.
-- DEAD ROUTE: threading the held candidate through the continuation's
--   STATE, beside the parent's.  The state type is what the candidate's
--   observable arm quantifies over, so a state holding a candidate sits
--   one universe above the quantifier, at every level the quantifier
--   is raised to.
-- DEAD ROUTE: a node-freshness family concluding that a subscribe
--   writes nothing below its own floor, spent to say the cell was
--   untouched across a def's subscription.  The connect refutes the
--   conclusion rather than blocking the proof -- it registers the
--   caller's continuation and then folds over it, so a subscription
--   does step a frame minted before it began, and the frame it steps
--   is exactly this one.
-- DEAD ROUTE: carrying the cell's candidate in the STATE RECORD, as a
--   field beside the nodes.  The candidate's observable arm is indexed
--   by the subscription relation, which is indexed by the state
--   record, so a field of that record naming the candidate is circular
--   however the modules are cut; stated as a precondition on the arm
--   it is the same cycle and does not decrease, since a store predicate
--   reaches the candidate at whatever type a node holds; stated as an
--   indexed family it is refused for positivity the moment the arm
--   ASSUMES it.  Parameterising the record over an abstract predicate
--   is that cycle deferred to the instantiation.  A SYNTACTIC invariant
--   that a stored value denotes a closed term is vacuous, reflection
--   being total.
-- RECOVERY: git show 33078215:agda/src/Rx/Evaluator/Freshness/Preserve.agda
--   is the freshness family, and `git show
--   33078215:agda/src/Rx/Evaluator/Freshness/Mono.agda` the
--   monotonicity it stood on.

Held : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → Set₁
Held {Γ = Γ} m u = Maybe (Σ (Val Γ u) (Red m u))

-- the held candidate, if it is for the value the store holds
certify : ∀ {n} {Γ : Ctx n} {m u} → Held {Γ = Γ} m u → (a : Val Γ u) → Maybe (Red m u a)
certify {u = u} nothing a = vouch u a
certify {u = u} (just (a′ , r)) a with eqVal u a a′
... | just refl = just r
... | nothing   = vouch u a

-- ONE READING OF THE CELL.  The dispatch it mirrors branches on a
-- lookup the goal does not mention, so the reading is taken as a
-- parameter -- and the certified held candidate is spent on the
-- accumulator that was found.
redScanDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                  {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
                → Held {Γ = Γ} m u → RedFn m fn → All (λ v → Maybe (Red m s v)) vals
                → All (λ v → Maybe (Red m u v))
                    (proj₁ (scanDispatch {e = e} fn nid vals fin sched st ns))
redScanDispatch {u = u} fn nid {vals} fin sched st (just (cell-st {w} a)) held rf cs
  with w ≟ᵗ u
... | no  _    = []
... | yes refl = proj₁ (redScanVals fn rf (certify held a) cs)
redScanDispatch fn nid fin sched st nothing                      held rf cs = []
redScanDispatch fn nid fin sched st (just (take-st _))           held rf cs = []
redScanDispatch fn nid fin sched st (just (batchSync-st _ _ _))  held rf cs = []
redScanDispatch fn nid fin sched st (just (mergeAll-st _ _ _ _)) held rf cs = []
redScanDispatch fn nid fin sched st (just (switch-st _ _))       held rf cs = []
redScanDispatch fn nid fin sched st (just (exhaust-st _ _))      held rf cs = []

-- THE BRACKET'S DISPATCH.  While the bit is up the frame emits
-- nothing and appends to the store's buffer; with the bit down the
-- regrouping is the arriving column.
redBatchDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s}
                   (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
                   (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
                 → All (λ v → Maybe (Red m s v)) vals
                 → All (λ v → Maybe (Red m (s ×ᵗ listᵗ s) v))
                     (proj₁ (batchDispatch {e = e} nid vals fin sched st ns))
redBatchDispatch {s = s} nid fin sched st (just (batchSync-st {w} true bur done)) cs
  with w ≟ᵗ s
... | no  _    = []
... | yes refl = []
redBatchDispatch nid fin sched st (just (batchSync-st false _ _)) cs = redBatchVals false cs
redBatchDispatch nid fin sched st (just (cell-st _))              cs = []
redBatchDispatch nid fin sched st (just (take-st _))              cs = []
redBatchDispatch nid fin sched st (just (mergeAll-st _ _ _ _))    cs = []
redBatchDispatch nid fin sched st (just (switch-st _ _))          cs = []
redBatchDispatch nid fin sched st (just (exhaust-st _ _))         cs = []
redBatchDispatch nid fin sched st nothing                         cs = []

-- THE FLUSH AT THE BOUNDARY reads the buffer out of the store, so its
-- entries are vouched only where their type does it for them.
redBatchBuf : ∀ {n} {Γ : Ctx n} {m} (s : Ty) (ns : Maybe (NodeState Γ))
            → All (λ v → Maybe (Red m (s ×ᵗ listᵗ s) v)) (proj₁ (batchBuf {Γ = Γ} s ns))
redBatchBuf s (just (batchSync-st {w} _ bur done)) with w ≟ᵗ s
... | no  _    = []
... | yes refl = redBatchVals true (vouchAll s bur)
redBatchBuf s (just (cell-st _))           = []
redBatchBuf s (just (take-st _))           = []
redBatchBuf s (just (mergeAll-st _ _ _ _)) = []
redBatchBuf s (just (switch-st _ _))       = []
redBatchBuf s (just (exhaust-st _ _))      = []
redBatchBuf s nothing                      = []

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
monus-sink : ∀ {n lo} (i : Fin n) → lo ≤ toℕ i → n ∸ suc (toℕ i) < n ∸ lo
monus-sink i below = ∸-monoʳ-< (s≤s below) (toℕ<n i)

------------------------------------------------------------------
-- THE FRAME CONTINUATIONS THAT REACH NO CYCLE.
------------------------------------------------------------------

-- THE ROOT MINTS THE BURST FROM NOTHING, and its state is the unit.
rootRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo} {P : Val Γ t → Set₁}
       → RP {e = e} m {lo = lo} P ⊤ root
fold rootRP tt now vals _ fin sched st rm = (_ , fold-root) , tt

-- EACH FRAME CONTINUATION IS ONE `fold-step` OVER ITS PARENT.  The
-- step produces no root emits of its own -- `stepFrame⇓` says so in
-- the constructor's index -- so the answer is the parent's answer, and
-- the derivation is the step's constructor over the parent's.

mapRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u lo ℓ S}
        (fn : FnClo Γ s u) → RedFn m fn → (h : lo ≤ ℓ) (κ : Path Γ ℓ u t)
      → RP {e = e} m (Red m u) S κ → RP {e = e} m (Red m s) S (map-f fn ↠[ h ] κ)
fold (mapRP fn rf h κ rp) s now vals cs fin sched st rm =
  let ((r , f) , s′) =
        fold rp s now (map (applyClo fn) vals) (redMapVals fn rf cs) fin sched st rm
  in (r , fold-step step-map f) , s′

takeRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ S}
         (nid : NodeId) (h : lo ≤ ℓ) (κ : Path Γ ℓ s t)
       → RP {e = e} m (Red m s) S κ → RP {e = e} m (Red m s) S (take-f nid ↠[ h ] κ)
fold (takeRP nid h κ rp) s now vals cs fin sched st rm =
  let ns = lookupNode nid (EvalSt.nodes st)
      (outs , fin′ , sched₁ , st₁) = takeDispatch nid vals fin sched st ns
      ((r , f) , s′) =
        fold rp s now outs (redTakeDispatch nid fin sched st ns cs) fin′ sched₁ st₁
          (room-keeps (takeDispatch-keeps nid vals fin sched st ns) rm)
  in (r , fold-step step-take f) , s′

-- THE FOLD CLOSES OVER ITS HELD ACCUMULATOR.  The subscribe arm builds
-- it with the initial accumulator and the candidate the term face
-- gives for it; every fold re-reads the store and certifies.
scanRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u lo ℓ S}
         (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId) → RedFn m fn → Held {Γ = Γ} m u
       → (h : lo ≤ ℓ) (κ : Path Γ ℓ u t)
       → RP {e = e} m (Red m u) S κ
       → RP {e = e} m (Red m s) S (scan-f fn nid ↠[ h ] κ)
fold (scanRP fn nid rf held h κ rp) s now vals cs fin sched st rm =
  let ns = lookupNode nid (EvalSt.nodes st)
      (outs , fin′ , sched₁ , st₁) = scanDispatch fn nid vals fin sched st ns
      ((r , f) , s′) =
        fold rp s now outs (redScanDispatch fn nid fin sched st ns held rf cs) fin′ sched₁ st₁
          (room-keeps (scanDispatch-keeps fn nid vals fin sched st ns) rm)
  in (r , fold-step step-scan f) , s′

-- THE BRACKET'S FLUSH is not here but in the subscribe arm, which is
-- the one place that sees the buffer after the bit goes down.
batchRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ S}
          (nid : NodeId) (h : lo ≤ ℓ) (κ : Path Γ ℓ (s ×ᵗ listᵗ s) t)
        → RP {e = e} m (Red m (s ×ᵗ listᵗ s)) S κ
        → RP {e = e} m (Red m s) S (batchSync-f nid ↠[ h ] κ)
fold (batchRP nid h κ rp) s now vals cs fin sched st rm =
  let ns = lookupNode nid (EvalSt.nodes st)
      (outs , fin′ , sched₁ , st₁) = batchDispatch nid vals fin sched st ns
      ((r , f) , s′) =
        fold rp s now outs (redBatchDispatch nid fin sched st ns cs) fin′ sched₁ st₁
          (room-keeps (batchDispatch-keeps nid vals fin sched st ns) rm)
  in (r , fold-step step-batchSync f) , s′

------------------------------------------------------------------
-- THE TWO DEAD BRANCHES, WHICH ARE THE WHOLE OF WHAT IS LEFT TO PROVE.
------------------------------------------------------------------

-- BOTH GUARDS ASK THE SAME QUESTION: HAS A CONNECT HAPPENED SINCE THIS
-- CEILING WAS SET?  A connect is the only thing that lowers the room,
-- and it is also the only thing that walks a registry path during a
-- subscribe -- so it is the only thing that can put an unvouched value
-- in front of a flattener, and the only thing that can grow a
-- flattener's queue behind a drain's back.  Where the guard finds the
-- room strictly under the ceiling, it peels the accessibility and
-- re-enters at the lower ceiling; where it does not, the state it is
-- standing in should be unreachable, and the branch is a leaf.
--
-- THE LEAVES ARE ON THE EXTRACTED PATH, WHICH IS THE POINT.  A
-- postulate here is not deferred debt: it is an evaluator that dies at
-- `postulate evaluated` the first time the branch is taken, so the
-- oracle decides in minutes whether the invariant behind each guard
-- holds across the corpus.  A branch that never fires is the proof
-- obligation and nothing else is; a branch that fires is a refutation
-- of the invariant, with the program that refutes it.

-- AN UNVOUCHED OBSERVABLE REACHED A FLATTENER WITH THE ROOM STILL AT
-- ITS CEILING.  The value came out of a store -- a fold's cell, a
-- bracket's buffer -- that a fold this subscribe never saw had
-- written; that fold was a fan-out; a fan-out is a connect; a connect
-- lowered the room.  So the room is under the ceiling and this branch
-- is dead.
--
-- THE SWEEP REACHES IT FROM THE SCHEDULE, WHICH THAT ARGUMENT MISSES.
-- `subs-defer` does not subscribe its body: it schedules the body as
-- an observable arriving at a `mergeAll` frame, and the arrival folds
-- the raw path with `vouchAll`, which vouches nothing at an
-- observable.  So `defer(of(5))` hands the flattener an unvouched
-- value with no share in the program, the room is zero, and this
-- branch is taken -- on 120 of the sweep's 500 cases.
--
-- IT ANSWERS THE SUBSCRIBE, NOT THE CONSUME, so the arm that reaches it
-- wraps it exactly as it wraps a paid hop and the relation cannot
-- tell the two apart.  Stated at full strength: a subscription of the
-- arriving observable down the exit frame's path, from the state the
-- consume built, at any ceiling.
--
-- PROBED: `Probed.Stuck-Branches` -- `of(5)` subscribed down a
--   `from-inner` exit frame to the root, at the initial state with the
--   flattener's node installed by hand, through the react, the finish's
--   fold and an empty drain.  Not covered: any state a run reached.
postulate
  stuck-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {S : Set}
              (o : Val Γ (obs u)) (κ′ : Path Γ lo u t) (now : Tick)
              (s : S) (sched : Sched Γ) (st : EvalSt e)
            → Room m sched st
            → ¬ (unconn (Sched.slots sched) (EvalSt.connectedShares st) < m)
            → Σ (Stream Γ t × Sched Γ × EvalSt e)
                (λ r → subscribeE⇓ {e = e} o κ′ now sched st r)
              × S

-- A FLATTENER'S QUEUE OUTGREW THE BUDGET THE DRAIN THAT SUBSCRIBED
-- THIS INNER SET FOR IT, WITH THE ROOM STILL AT ITS CEILING.  A walk-
-- order inner is subscribed with a lane free, and a lane is free only
-- while the queue is empty; a drained inner is subscribed with the
-- queue's remaining length as its budget.  Either way the queue at
-- this inner's synchronous end is within the budget unless something
-- enqueued during the inner's own subscribe, and only a fan-out
-- through the flattener's outer frame can -- a connect.  So the room
-- is under the ceiling and this branch is dead.
--
-- IT ANSWERS THE DRAIN THE FINISH RUNS, at full strength: the queue
-- spent from the state the finish folded into, with the lane already
-- lowered, at any ceiling.
--
-- PROBED: `Probed.Stuck-Branches` -- the empty queue only, which is
--   degenerate.  Not covered: a nonempty queue, the one shape that
--   subscribes anything.
postulate
  stuck-finish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo} {S : Set}
                 (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
                 (s₀ : S) (sched : Sched Γ) (st : EvalSt e)
                 (lim : Maybe ℕ) (act : ℕ) (q : List (Val Γ (obs s))) (od : Bool)
               → Room m sched st
               → ¬ (unconn (Sched.slots sched) (EvalSt.connectedShares st) < m)
               → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
                   (λ r → mergeAllDrain⇓ {e = e} allNid κ now q lim (pred act) od q
                            sched st r)
                 × S

------------------------------------------------------------------
-- THE BODY, AND WHAT PAYS FOR IT.
------------------------------------------------------------------

-- THE EXPRESSION FACE AND THE TERM FACE ARE ONE RECURSION: a term
-- embeds an expression and an operator carries terms, so neither can
-- be a leaf beside the other without claiming the whole theorem.  Both
-- recurse on the ACCESSIBILITY of the guarded size, which counts an
-- operator's spine and the terms it carries and stops at the gate;
-- every call below hands on a strictly smaller size, the fixpoint arm
-- included.
--
-- THE ONE ARM WITH NO SUBTERM IS THE μ, AND THE SYNTAX PAYS FOR IT.
-- An unfolding is no subterm of its fixpoint and sits at the same
-- type, so neither the syntax nor the candidate's own type recursion
-- reaches it.  What does is the size: the μ former spends a unit, the
-- gate the μ variable must sit behind is where the size stops looking,
-- and the unfolding therefore has exactly the size the body had.
--
-- THE INPUT CEILING IS A MEASURE COMPONENT, NOT A HYPOTHESIS.  The
-- walk carries a stratum `k` with the guard `T (inputsBelowᵉ k b)` and
-- an `Acc` on it, ordered ABOVE the g-size accessibility.  A term step
-- holds the ceiling and shrinks the size; the SHARED-SLOT step drops
-- the ceiling to the slot's own index -- which its `ok` field licenses
-- -- and lets the size go free.

-- AND ABOVE BOTH SITS THE ROOM, WHICH IS WHAT THE FLATTENER'S TWO
-- RE-ENTRIES AND THE SHARE'S FAN-OUT DESCEND ON.  The measure the
-- checker reads is lexicographic: the room's accessibility outermost,
-- then the drain budget's, then the descents each family already had
-- -- the input ceiling and the guarded size, the fuel and walk and
-- registry lists, the path, the floor.  Four edges are strict in the
-- room: the connect, the two guards, and nothing else; one edge is
-- strict in the budget at an unchanged room: a drained inner's
-- synchronous end.  Every other edge holds both, and the cycles the
-- checker must close each pass one of the five.  The checker does not
-- need to be told the order; it needs every strict edge to be an
-- application of the accessibility's own field, which each one is.

-- THE CANDIDATE AT VALUES IS SATURATED WHEREVER IT IS CALLED.  It
-- takes the ceiling's accessibility, and it is called at exactly three
-- kinds of site: a flattener's drain, on an observable the queue kept;
-- a guard, on an unvouched observable, with the accessibility peeled;
-- and a raw fold, on a closure or a cell a registry path reads, at the
-- ceiling the fan-out's peel funded.  No column of unapplied
-- candidates is built anywhere.

redExpAcc : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t)
            (ρ : Env Γ Θ) {m} → RedEnv m ρ
          → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
          → Acc _<_ (gsizeᵉ b) → Acc _<_ m → Red {Γ = Γ} m (obs t) (Θ , b , ρ)

-- THE SLOT ARM, WHICH IS SEVERAL SUB-ARMS OF PROTOCOL AND ONE THAT
-- SPENDS THE CEILING.  It mirrors the machine's own case split on
-- the slot exactly, because the derivation it must produce is the
-- one the machine produces; every source arm hands its values to the
-- continuation with `red-data` beside them, and the scripted slot's
-- side condition is what `red-data` runs on.
red-input : ∀ {n} {Γ : Ctx n} {Θ} (i : Fin n) (ρ : Env Γ Θ) (k : ℕ)
          → T (toℕ i <ᵇ k) → Acc _<_ k → ∀ {m} → Acc _<_ m
          → Red {Γ = Γ} m (obs (lookup Γ i)) (Θ , input i , ρ)

-- THE SLOT SUB-ARM THE OTHERS ARE NOT, AND THE ONE EDGE OF THE CYCLE
-- THAT SPENDS THE ROOM.  A share's definition is an arbitrary
-- expression standing in no relation to `input i`, so it cannot be
-- reached by any descent on the TERM; the telescope's side condition
-- charges it against the input ceiling `toℕ i` instead.  And it is
-- subscribed at the sink, with the RAW continuation above it: the
-- def's values fan out over the registry, through paths no subscribe
-- built, at the ceiling the connect just lowered to -- which is what
-- funds every `red-val` the raw walk makes.  The trigger's own
-- continuation is not used at all; the trigger receives its values
-- through the chain it registered, the way a joiner does, so the
-- continuation's state comes back untouched.
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
    × S

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

-- A FRAME'S CLOSURE APPLIED is the term face at one more entry, and
-- with the environment carried rather than substituted that is all
-- it is -- no transport, no lemma, the two statements are the same
-- statement.
redFnAcc : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Tm Γ [] [] (s ∷ Θ) u)
           (ρ : Env Γ Θ) {m} → RedEnv m ρ
         → (k : ℕ) → T (inputsBelowᵗ k f) → Acc _<_ k
         → Acc _<_ (gsizeᵗ f) → Acc _<_ m → RedFn {Γ = Γ} m {s = s} {u = u} (_ , f , ρ)

-- THE TOP LINE: every closure whose environment is reducible is
-- itself reducible, which is the face above with both accessibilities
-- seeded at their own subjects and the room's taken as given.
--
-- THE SUBSCRIBE CYCLE DESCENDS LEXICOGRAPHICALLY ON ACCESSIBILITIES IT
-- CARRIES.  The room's is outermost and only a share's connect peels
-- it; under it the input bound and the term size fall at every former,
-- and an environment is walked entry by entry.  Every member takes the
-- room's accessibility as an argument, so the checker reads the whole
-- order off the call sites.
-- STRUCTURAL SCC: dispatchShare! rawRP red-env red-input red-input-shared red-val redExpAcc redFnAcc redTmAcc redTmsAcc reducible shareGo! shareWalk!
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
--
-- WHAT THE ROOM DOES NOT FUND, AND WHAT DOES.  The room is the
-- OUTERMOST component and a connect is the only thing that moves it,
-- so a backlog spent in a program with no share in it -- room zero at
-- every state -- is spent under the NEXT component: a drained inner is
-- subscribed with the queue's remaining length as its budget, at the
-- same room, and a finish reconciles the queue against that budget
-- before it drains.  A bounded merge whose lane queues with no share
-- in the program is funded here without a peel.  The room is asked for
-- a strict step only where a value the store chose reaches a subscribe
-- with no candidate and no budget covers it -- which is where the two
-- guards stand.
--
-- DEAD ROUTE: PARKING the claim -- a refused arrival handed back
--   beside its value as a return rather than written into the store,
--   so that the spend applies a candidate it was given.  Green alone;
--   it stops being green beside a path-indexed cell ledger, since the
--   parked row has to carry the ledger standing at the path it will be
--   spent at and so reaches itself to the left of an arrow.
-- DEAD ROUTE: STRATIFYING the candidate -- a bound on it, and a store
--   value served by an oracle for every smaller bound.  A bound carried
--   as a `<` hypothesis is a proof term the termination checker does
--   not read, so the only form that checks steps the bound down by one
--   at each use, which is a counter the run spends.
-- DEAD ROUTE: INDEXING the candidate by the room ALONE, so that every
--   read the store serves is funded by an invariant saying the queue
--   holding it witnesses a strict fall.  Refuted outright: the room
--   counts SHARED slots, and a bounded merge over two inners fills its
--   lane's queue with no share in the program.
-- DEAD ROUTE: a LEDGER for the flattener's backlog, as a cell ledger
--   for a scan.  A queue entry is an observable at the element type,
--   so its claim wants a path at that type, and the frame an inner's
--   spend stands on is one level BELOW it; stated at the outer's frame
--   it is a SIBLING of the spend's, on no path the spend holds.
-- REFUTED: `Refuted.Room-Backlog`
red-val : ∀ {n} {Γ : Ctx n} {m} → Acc _<_ m → (t : Ty) (v : Val Γ t) → Red m t v

red-env : ∀ {n} {Γ : Ctx n} {m} → Acc _<_ m → {Θ : List Ty} (ρ : Env Γ Θ) → RedEnv m ρ

-- CONSUMING ONE ARRIVING OBSERVABLE.  What a consume decides is
-- whether the observable is taken at all, and every operator answers
-- that off the store.  Taken, the observable is subscribed with the
-- inner's frame pushed onto the continuation; its synchronous values,
-- its synchronous end and everything either causes are folded where
-- they are produced, so the consume's answer is the subscribe's
-- answer and nothing is reacted to afterwards.
--
-- THE HOP IS PAID BY THE ARRIVING VALUE'S OWN CANDIDATE where it has
-- one, and by the guard where it has none.  The candidate quantifies
-- over every state under the ceiling, so the freshly-counted schedule
-- this arm builds is one of them by construction.
red-consume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo S}
              (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
              (now : Tick) (o : Val Γ (obs u)) → Maybe (Red m (obs u) o)
            → RP {e = e} m (Red m u) S κ → S
            → ∀ (sched : Sched Γ) (st : EvalSt e)
            → Acc _<_ m → Room m sched st
            → Σ (Stream Γ t × Sched Γ × EvalSt e)
                (λ r → thruConsume⇓ {e = e} op nid κ now o sched st r)
              × S

-- THE HOP ITSELF, PAID TWO WAYS.  With a candidate in hand the
-- arriving observable is applied to the exit frame's continuation,
-- built at this ceiling's accessibility.  Without one the room is
-- compared against the ceiling: strictly below it, the accessibility
-- peels, the fundamental theorem at values is invoked at the lower
-- ceiling, and the continuation is DROPPED to it -- its candidates
-- forgotten, since they were stated at the higher ceiling -- with
-- reflexivity as the new room witness.  At the ceiling, the branch is
-- dead and `stuck-hop` says so.  The exit frame is built HERE, at
-- whichever accessibility this hop ends up holding, and not handed in
-- as a builder: a builder is a lambda over an accessibility, and the
-- checker can relate a lambda's bound accessibility to nothing.
red-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo S}
          (op : AllOp) (nid inst : NodeId) (κ : Path Γ lo u t) (now : Tick)
          (o : Val Γ (obs u)) → Maybe (Red m (obs u) o)
        → RP {e = e} m (Red m u) S κ → S
        → (sched : Sched Γ) (st : EvalSt e)
        → Acc _<_ m → Room m sched st
        → Σ (Stream Γ t × Sched Γ × EvalSt e)
            (λ r → subscribeE⇓ {e = e} o (from-inner op nid inst ↠[ ≤-refl ] κ)
                     now sched st r)
          × S

-- THE DRAIN A FINISH RUNS, RECONCILED AGAINST THE BUDGET IT WAS
-- HANDED.  A walk-order or drained finish holds the budget its
-- subscriber set: the queue's length equal to it
-- reuses the accessibility unchanged; shorter peels it; longer means
-- something enqueued during this inner's own subscribe, which only a
-- fan-out through the flattener's outer frame does, and that is a
-- connect -- so the room is compared against the ceiling, the
-- accessibility peels there instead, and the ceiling's continuation
-- is dropped to the new one.  At the ceiling the branch is dead.
finishDrain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
               (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
               (lim : Maybe ℕ) (act : ℕ) (od : Bool) (q : List (Val Γ (obs s)))
             → RP {e = e} m (Red m s) S κ → S
             → (sched : Sched Γ) (st : EvalSt e)
             → Acc _<_ m → (k : ℕ) → Acc _<_ k → Room m sched st
             → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
                 (λ r → mergeAllDrain⇓ {e = e} allNid κ now q lim (pred act) od q
                          sched st r)
               × S

-- EACH PEEL MATCHES ITS OWN ACCESSIBILITY, so that no branch rebuilds
-- one it matched: a rebuilt accessibility across a `with` reads to the
-- checker as unrelated to the one the clause was handed.
finishPeelQ! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
               (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
               (lim : Maybe ℕ) (act : ℕ) (od : Bool) (q : List (Val Γ (obs s)))
             → RP {e = e} m (Red m s) S κ → S
             → (sched : Sched Γ) (st : EvalSt e)
             → Acc _<_ m → (k : ℕ) → Acc _<_ k → Room m sched st
             → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
                 (λ r → mergeAllDrain⇓ {e = e} allNid κ now q lim (pred act) od q
                          sched st r)
               × S

finishPeelM! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
               (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
               (lim : Maybe ℕ) (act : ℕ) (od : Bool) (q : List (Val Γ (obs s)))
             → RP {e = e} m (Red m s) S κ → S
             → (sched : Sched Γ) (st : EvalSt e)
             → Acc _<_ m → Room m sched st
             → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
                 (λ r → mergeAllDrain⇓ {e = e} allNid κ now q lim (pred act) od q
                          sched st r)
               × S

-- THE WALK IS THE CONSUME THREADED, and the answer is the
-- concatenation of the answers each arrival produced.
red-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo S}
           (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
           (now : Tick) (vals : List (Val Γ (obs u)))
         → All (λ o → Maybe (Red m (obs u) o)) vals
         → RP {e = e} m (Red m u) S κ → S
         → ∀ (sched : Sched Γ) (st : EvalSt e)
         → Acc _<_ m → Room m sched st
         → Σ (Stream Γ t × Sched Γ × EvalSt e)
             (λ r → thruWalk⇓ {e = e} op nid κ now vals sched st r)
           × S

-- THE FLATTENER'S OUTER FRAME AS A CONTINUATION.  Its fold is the walk
-- and then the wrap; the residual it hands its parent is empty, since
-- every value it received became a subscription that already folded.
thruRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ S}
         (op : AllOp) (nid : NodeId) → Acc _<_ m
       → (h : lo ≤ ℓ) (κ : Path Γ ℓ u t)
       → RP {e = e} m (Red m u) S κ
       → RP {e = e} m (Red m (obs u)) S (thru-outer op nid ↠[ h ] κ)

-- THE INNER'S EXIT FRAME AS A CONTINUATION, WHICH IS WHERE THE DRAIN
-- BUDGET LIVES.  A value folded through it is the inner delivering; a
-- completion folded through it is the inner ending, which frees a
-- lane and may drain the queue.  The budget is the accessibility the
-- drain that subscribed this inner peeled for it: the length of the
-- queue that drain still had to spend, so that a synchronous end
-- inside a drained subscribe nests its own drain strictly under the
-- outer one.  A walk-order inner has budget zero, because a walk-order
-- inner is subscribed with a lane free and the queue empty.
fromInnerRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ S}
              (op : AllOp) (allNid inst : NodeId) → Acc _<_ m
            → (k : ℕ) → Acc _<_ k
            → (h : lo ≤ ℓ) (κ : Path Γ ℓ s t)
            → RP {e = e} m (Red m s) S κ
            → RP {e = e} m (Red m s) S (from-inner op allNid inst ↠[ h ] κ)

-- A RAW PATH'S EXIT FRAME IS ITS OWN BUILDER, WITH NO BUDGET.  One the
-- registry holds, walked by a tick or a fan-out, seeds the drain's
-- budget fresh at the end, since every cycle through a raw path passes
-- the fan-out's peel of the room.  It is a separate builder, and its
-- react and finish separate functions, so that the budgeted cycle
-- never re-seeds: a flag would put the fresh seed on the same edge the
-- budget descends along, and the checker cannot read the flag.
fromInnerRawRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ S}
                 (op : AllOp) (allNid inst : NodeId) → Acc _<_ m
               → (h : lo ≤ ℓ) (κ : Path Γ ℓ s t)
               → RP {e = e} m (Red m s) S κ
               → RP {e = e} m (Red m s) S (from-inner op allNid inst ↠[ h ] κ)

-- A WALK-ORDER INNER'S EXIT FRAME HAS NO BUDGET EITHER, because it
-- needs none: it is subscribed with a lane free and the queue empty,
-- so at its end the queue is empty -- nothing to drain -- or it grew
-- during the inner's own subscribe, which only a connect does, and
-- the room peels.  A budget seeded here would put a fresh one on a
-- cycle whose room has not moved.
fromInnerWalkRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ S}
                  (op : AllOp) (allNid inst : NodeId) → Acc _<_ m
                → (h : lo ≤ ℓ) (κ : Path Γ ℓ s t)
                → RP {e = e} m (Red m s) S κ
                → RP {e = e} m (Red m s) S (from-inner op allNid inst ↠[ h ] κ)

-- ONE INNER SUBSCRIPTION, OPENED AT A FRESHLY COUNTED INSTANCE, BY THE
-- CANDIDATE AT VALUES.  The drain is the one place an observable is
-- subscribed with no candidate to hand and no fan-out to fund it; the
-- budget it passes down is what the checker reads instead.
inner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
         (op : AllOp) (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
         (o : Val Γ (obs s))
       → RP {e = e} m (Red m s) S κ → S
       → (sched : Sched Γ) (st : EvalSt e)
       → Acc _<_ m → (k : ℕ) → Acc _<_ k → Room m sched st
       → Σ (NodeId × Stream Γ t × Sched Γ × EvalSt e)
           (λ r → subscribeInner⇓ {e = e} op allNid κ now o sched st r)
         × S

-- THE PARKED LANE, HANDED BACK ITS QUEUE.  A flattener that could not
-- subscribe when a value arrived kept it; this is the walk that spends
-- the backlog once a lane frees.  The queue is re-read from the node
-- between spends, so the list this recursion peels is a BOUND on the
-- iterations and not the work itself -- and its accessibility is what
-- each spent inner inherits as its budget.
mergeAllDrain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
                 (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
                 (fuel : List (Val Γ (obs s)))
                 (lim : Maybe ℕ) (act : ℕ) (od : Bool)
                 (q : List (Val Γ (obs s)))
               → RP {e = e} m (Red m s) S κ → S
               → (sched : Sched Γ) (st : EvalSt e)
               → Acc _<_ m → Acc _<_ (length fuel) → Room m sched st
               → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
                   (λ r → mergeAllDrain⇓ {e = e} allNid κ now fuel lim act od q sched st r)
                 × S

-- A FIN COMPLETES AN INNER ONLY ONCE NOTHING UNDER ITS EXIT FRAME CAN
-- DELIVER AGAIN, and only a merge's finish subscribes anything -- it
-- folds the dying inner's last values up the continuation, then drains
-- the queue the lane limit had held back.  The residual it hands the
-- exit frame's parent is the completion flag alone.
--
-- THE BUDGET IS RECONCILED AGAINST THE QUEUE HERE.  Equal, the
-- accessibility is the drain's outright; below, it is peeled; above
-- -- the queue grew during this inner's subscribe -- the room guard
-- decides, because only a connect grows a queue behind a drain.
innerFinish! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
               (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
               (now : Tick) (vals : List (Val Γ s))
             → All (λ v → Maybe (Red m s v)) vals
             → RP {e = e} m (Red m s) S κ → S
             → (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
             → Acc _<_ m → (k : ℕ) → Acc _<_ k → Room m sched st
             → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
                 (λ r → innerFinish⇓ {e = e} op allNid inst κ now vals sched st ns r
                        × All (λ v → Maybe (Red m s v)) (proj₁ (proj₂ r)))
               × S

innerReact! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
              (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
              (now : Tick) (vals : List (Val Γ s))
            → All (λ v → Maybe (Red m s v)) vals
            → RP {e = e} m (Red m s) S κ → S
            → (sched : Sched Γ) (st : EvalSt e) (fin : Bool)
            → Acc _<_ m → (k : ℕ) → Acc _<_ k → Room m sched st
            → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
                (λ r → innerReact⇓ {e = e} op allNid inst κ now vals sched st fin r
                       × All (λ v → Maybe (Red m s v)) (proj₁ (proj₂ r)))
              × S

innerFinishRaw! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
                  (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
                  (now : Tick) (vals : List (Val Γ s))
                → All (λ v → Maybe (Red m s v)) vals
                → RP {e = e} m (Red m s) S κ → S
                → (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
                → Acc _<_ m → Room m sched st
                → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
                    (λ r → innerFinish⇓ {e = e} op allNid inst κ now vals sched st ns r
                           × All (λ v → Maybe (Red m s v)) (proj₁ (proj₂ r)))
                  × S

innerReactRaw! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
                 (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
                 (now : Tick) (vals : List (Val Γ s))
               → All (λ v → Maybe (Red m s v)) vals
               → RP {e = e} m (Red m s) S κ → S
               → (sched : Sched Γ) (st : EvalSt e) (fin : Bool)
               → Acc _<_ m → Room m sched st
               → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
                   (λ r → innerReact⇓ {e = e} op allNid inst κ now vals sched st fin r
                          × All (λ v → Maybe (Red m s v)) (proj₁ (proj₂ r)))
                 × S

innerFinishWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
                  (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
                  (now : Tick) (vals : List (Val Γ s))
                → All (λ v → Maybe (Red m s v)) vals
                → RP {e = e} m (Red m s) S κ → S
                → (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
                → Acc _<_ m → Room m sched st
                → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
                    (λ r → innerFinish⇓ {e = e} op allNid inst κ now vals sched st ns r
                           × All (λ v → Maybe (Red m s v)) (proj₁ (proj₂ r)))
                  × S

innerReactWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
                 (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
                 (now : Tick) (vals : List (Val Γ s))
               → All (λ v → Maybe (Red m s v)) vals
               → RP {e = e} m (Red m s) S κ → S
               → (sched : Sched Γ) (st : EvalSt e) (fin : Bool)
               → Acc _<_ m → Room m sched st
               → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
                   (λ r → innerReact⇓ {e = e} op allNid inst κ now vals sched st fin r
                          × All (λ v → Maybe (Red m s v)) (proj₁ (proj₂ r)))
                 × S

finishWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo S}
               (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
               (lim : Maybe ℕ) (act : ℕ) (od : Bool) (q : List (Val Γ (obs s)))
             → RP {e = e} m (Red m s) S κ → S
             → (sched : Sched Γ) (st : EvalSt e)
             → Acc _<_ m → Room m sched st
             → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
                 (λ r → mergeAllDrain⇓ {e = e} allNid κ now q lim (pred act) od q
                          sched st r)
               × S

-- THE RAW CONTINUATION: A REGISTRY PATH, WALKED WITH NO CANDIDATES IN
-- HAND.  A tick walks one from the top with the room's accessibility
-- seeded fresh, which is free; a fan-out walks one at the ceiling the
-- connect just peeled to, which is what pays for everything below.
-- It is built by recursion on the path, so each frame's continuation
-- is the frame's own builder over the raw continuation of the rest --
-- with the candidates the builder wants supplied by `red-val` and
-- `red-env` at this ceiling: a closure's environment at a map, a
-- closure's environment and NO held cell at a fold, nothing at a take
-- or a bracket, and the guard's own peel at a flattener.  Its state is
-- the unit, because nothing above a registry path is waiting to read
-- anything back.
--
-- AND THE FOLD'S RAW CONTINUATION HOLDS NO CELL BY DESIGN.  The store
-- has the accumulator, and re-deriving its candidate by running it is
-- the cycle this module exists not to close; so a raw fold through a
-- fold frame emits unvouched values, and the first flattener above it
-- pays the guard -- funded, because the raw walk is a fan-out and the
-- fan-out peeled.  A data-typed accumulator costs nothing either way.
rawRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
        (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
      → (κ : Path Γ ℓ u t) → RP {e = e} m (Red m u) ⊤ κ

-- THE FAN-OUT'S THREE, AND THE FLOOR THEY DESCEND ON.  A chain
-- registered on a share sinks STRICTLY above that share, so the room
-- left above the floor is what every hop through the share spends and
-- the path itself never has to.  The dispatch is the one edge that
-- takes a step of it, through `monus-sink`.
dispatchShare! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo} {i : Fin n}
                 (ac : Acc _<_ (n ∸ suc (toℕ i))) (below : lo ≤ toℕ i)
                 (now : Tick) (vals : List (Val Γ _)) (fin : Bool)
                 (sched : Sched Γ) (st : EvalSt e)
               → Acc _<_ m → Room m sched st
               → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
                   dispatchShare⇓ {e = e} now i below vals fin sched st r

shareWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {i : Fin n}
             (ac : Acc _<_ (n ∸ suc (toℕ i))) (now : Tick)
             (vals : List (Val Γ _)) (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e)
           → Acc _<_ m → Room m sched st
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               shareWalk⇓ {e = e} now i vals fin sched st r

shareGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {i : Fin n}
           (ac : Acc _<_ (n ∸ suc (toℕ i))) (now : Tick)
           (vals : List (Val Γ _)) (fin : Bool)
           (ps : List (RegId × Path Γ (suc (toℕ i)) _ t))
           (sched : Sched Γ) (st : EvalSt e)
         → Acc _<_ m → Room m sched st
         → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
             shareGo⇓ {e = e} now i vals fin ps sched st r

------------------------------------------------------------------
-- THE EXPRESSION FACE.
------------------------------------------------------------------

-- EVERY SOURCE ARM FOLDS ITS BURST THROUGH THE CONTINUATION, and every
-- transformer arm pushes its frame onto it and subscribes its source.
-- What used to be the push through the frame after the subscribe is
-- now inside the frame's continuation, one value group at a time, in
-- the order the values were produced.
redExpAcc (input i) ρ rρ k ok aK a aM = red-input i ρ k ok aK aM
redExpAcc (ofᵉ ts) ρ rρ k ok aK (acc rs) aM κ rp s now sched st rm =
  let ((r , f) , s′) =
        fold rp s now (map (λ tm → evalWith tm ρ) ts)
          (allJust (redTmsAcc ts ρ rρ k ok aK (rs ≤-refl) aM)) true sched st rm
  in (r , subs-of f) , s′
redExpAcc emptyᵉ ρ rρ k ok aK a aM κ rp s now sched st rm =
  let ((r , f) , s′) = fold rp s now [] [] true sched st rm
  in (r , subs-empty f) , s′
redExpAcc (mapᵉ {s = s} f b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let okf = ∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
      okb = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
      rf  = redFnAcc f ρ rρ k okf aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM
      ((r , d) , s₁) =
        redExpAcc b ρ rρ k okb aK
          (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f)))) aM
          (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) (mapRP (_ , f , ρ) rf ≤-refl κ rp) s₀
          now sched st rm
  in (r , subs-map d) , s₁
redExpAcc (takeᵉ c b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm
  with evalWith c ρ in ceq
... | zero  =
  let ((r , f) , s′) = fold rp s₀ now [] [] true sched st rm
  in (r , subs-take-zero ceq f) , s′
... | suc j =
  let okb = ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok
      nid = freshId nodeᵏ (Sched.mint sched)
      ((r , d) , s₁) =
        redExpAcc b ρ rρ k okb aK
          (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c)))) aM
          (take-f nid ↠[ ≤-refl ] κ) (takeRP nid ≤-refl κ rp) s₀ now
          (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
          (installNode nid (take-st (suc j)) st) rm
  in (r , subs-take-suc ceq refl d) , s₁

-- THE BRACKET IS OPENED BY THE INSTALL AND CLOSED WHEN THE SUBSCRIBE
-- CALL RETURNS, WHICH IS WHERE THE BIT GOES DOWN AND THE GROUP LEAVES.
-- The flush reads the buffer out of the store and folds the group up
-- the parent continuation -- the one fold this arm makes itself.
redExpAcc (batchSyncᵉ {t = u} b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((( out₁ , sched₁ , st₁) , d) , s₁) =
        redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
          (batchSync-f nid ↠[ ≤-refl ] κ) (batchRP nid ≤-refl κ rp) s₀ now
          (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
          (installNode nid (batchSync-st {s = u} true [] false) st) rm
      ns = lookupNode nid (EvalSt.nodes st₁)
      ((( out₂ , sched₂ , st₂) , f) , s₂) =
        fold rp s₁ now (proj₁ (batchBuf u ns)) (redBatchBuf u ns) (proj₂ (batchBuf u ns))
          sched₁ (installNode nid (batchSync-st {s = u} false [] false) st₁)
          (room-keeps (subscribeE-keeps d) rm)
  in ((out₁ ++ out₂ , sched₂ , st₂) , subs-batchSync refl d f) , s₂

-- THE FOLD BUILDS ITS CONTINUATION OVER THE INITIAL ACCUMULATOR AND
-- THE TERM FACE'S CANDIDATE FOR IT; what the store does to the cell
-- afterwards is the continuation's business, entry by entry.
redExpAcc (scanᵉ {s = s} {t = u} f z b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let zbe = inputsBelowᵗ k z ∧ inputsBelowᵉ k b
      okf = ∧ˡ (inputsBelowᵗ k f) zbe ok
      rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
      okz = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
      okb = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
      nid = freshId nodeᵏ (Sched.mint sched)
      rf  = redFnAcc f ρ rρ k okf aK
              (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵗ z + gsizeᵉ b)))) aM
      rz  = redTmAcc z ρ rρ k okz aK
              (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b))
                                (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f))))) aM
      ((r , d) , s₁) =
        redExpAcc b ρ rρ k okb aK
          (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z))
                            (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f))))) aM
          (scan-f (_ , f , ρ) nid ↠[ ≤-refl ] κ)
          (scanRP (_ , f , ρ) nid rf (just (evalWith z ρ , rz)) ≤-refl κ rp) s₀ now
          (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
          (installNode nid (cell-st (evalWith z ρ)) st) rm
  in (r , subs-scan refl d) , s₁
redExpAcc (mergeAllᵉ lim b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((r , d) , s₁) =
        redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
          (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ) (thruRP mergeAllᵒ nid aM ≤-refl κ rp) s₀ now
          (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
          (installNode nid (mergeAll-st lim 0 [] false) st) rm
  in (r , subs-merge-all (sub-all refl d)) , s₁
redExpAcc (switchAllᵉ b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((r , d) , s₁) =
        redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
          (thru-outer switchᵒ nid ↠[ ≤-refl ] κ) (thruRP switchᵒ nid aM ≤-refl κ rp) s₀ now
          (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
          (installNode nid (switch-st nothing false) st) rm
  in (r , subs-switch-all (sub-all refl d)) , s₁
redExpAcc (exhaustAllᵉ b) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((r , d) , s₁) =
        redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
          (thru-outer exhaustᵒ nid ↠[ ≤-refl ] κ) (thruRP exhaustᵒ nid aM ≤-refl κ rp) s₀ now
          (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
          (installNode nid (exhaust-st false false) st) rm
  in (r , subs-exhaust-all (sub-all refl d)) , s₁
redExpAcc (μᵉ body) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let ((r , d) , s₁) =
        redExpAcc (unfoldμ body) ρ rρ k (ib-unfoldμ k body ok) aK
          (rs (subst (_< suc (gsizeᵉ body))
                     (sym (gsize-unfoldμ body)) ≤-refl)) aM
          κ rp s₀ now sched st rm
  in (r , subs-μ d) , s₁
redExpAcc (varᵉ ()) ρ rρ k ok aK a aM
redExpAcc (deferᵉ body) ρ rρ k ok aK a aM κ rp s₀ now sched st rm =
  (_ , subs-defer refl refl refl refl) , s₀
redExpAcc (mintᵉ body) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm =
  let src = freshId sourceᵏ (Sched.mint sched)
      ((r , d) , s₁) =
        redExpAcc body (src ∷ᵉ ρ) (tt , rρ) k ok aK (rs ≤-refl) aM κ rp s₀ now
          (record sched
             { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
          st rm
  in (r , subs-mint refl d) , s₁

-- THE SLOT ARMS.  Each scripted arm folds what the slot script says
-- through the continuation, with `red-data` beside every value; the
-- live hot registers and folds nothing; the cold-with-a-tail registers
-- FIRST and then folds its prefix, since a synchronous value can cut
-- this very chain and a cut severs registrations.
red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ rp s now sched st rm
    with toℕ i <? lo
... | no  ¬below =
      let ((r , f) , s′) = fold rp s now [] [] true sched st rm
      in (r , subs-floor (≮⇒≥ ¬below) f) , s′
... | yes below  with Sched.slots sched i in slEq
...   | scripted {ok = okD} (hot async)
        with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
...     | true  =
          let ((r , f) , s′) = fold rp s now [] [] true sched st rm
          in (r , subs-hot-done below slEq doneEq f) , s′
...     | false = (_ , subs-hot-live below slEq doneEq refl) , s
red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ rp s now sched st rm
    | yes below | scripted {ok = okD} (cold sync []) =
      let ((r , f) , s′) = fold rp s now sync (allJust (redDatas _ _ okD sync)) true sched st rm
      in (r , subs-cold-sync below slEq f) , s′
red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ rp s now sched st rm
    | yes below | scripted {ok = okD} (cold sync (d ∷ ds)) =
      let rid = freshId regᵏ (Sched.mint sched)
          ((r , f) , s′) =
            fold rp s now sync (allJust (redDatas _ _ okD sync)) false
              (record sched
                 { mint = setAt regᵏ (suc rid)
                            (setAt sourceᵏ (suc (freshId sourceᵏ (Sched.mint sched)))
                              (setAt ordinalᵏ (suc (freshId ordinalᵏ (Sched.mint sched)))
                                (Sched.mint sched)))
                 ; live = record { source = freshId sourceᵏ (Sched.mint sched)
                                 ; ordinal = freshId ordinalᵏ (Sched.mint sched)
                                 ; elemTy = lookup Γ i
                                 ; pending = resolve now (d ∷ ds) }
                          ∷ Sched.live sched })
              (register rid (atDyn (freshId sourceᵏ (Sched.mint sched)) lo) κ st)
              (room-keeps (keeps-refl (Sched.slots sched) (EvalSt.connectedShares st)) rm)
      in (r , subs-cold-async below slEq refl refl refl f) , s′
red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ rp s now sched st rm
    | yes below | shared d {ok = okd} =
      red-input-shared i d (rsK (<ᵇ⇒< (toℕ i) k ok)) ρ
        κ below rp s now sched slEq st aM rm

-- THE CONNECT PEELS THE ROOM AND SUBSCRIBES THE DEF UNDER THE RAW
-- CONTINUATION AT THE SINK.  The count drops strictly across this arm
-- on exactly the two facts it already binds -- the slot's `shared`
-- shape and the membership reading `false` -- so the peel is the
-- accessibility's own field at that fall, and the ceiling below it is
-- the count as it stands after the insert, witnessed by reflexivity.
-- Everything the def's values reach is reached raw, at that ceiling.
red-input-shared {n = n} {Γ = Γ} {t = t} {lo = lo} i d {okd} aI ρ κ below rp s now sched slEq st (acc rsM) rm
    with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
... | true =
      let ((r , f) , s′) = fold rp s now [] [] true sched st rm
      in (r , subs-shared {κ = κ} {below = below} slEq
                (slot-spent {κ = κ} {below = below} doneEq f)) , s′
... | false
      with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
...   | true =
        (_ , subs-shared {κ = κ} {below = below} slEq
               (slot-join {κ = κ} {below = below} doneEq connEq refl)) , s
...   | false =
        let fall = ≤-trans (unconn-insert (Sched.slots sched)
                              (EvalSt.connectedShares st) i slEq connEq) rm
            aM′  = rsM fall
            rid  = freshId regᵏ (Sched.mint sched)
            ((r , dv) , _) =
              redExpAcc d []ᵉ tt (toℕ i) okd aI (<-wellFounded (gsizeᵉ d)) aM′
                (share-sink i ≤-refl)
                (rawRP (<-wellFounded (n ∸ toℕ i)) ≤-refl aM′ (share-sink i ≤-refl)) tt now
                (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                (register rid (atSlot i) (lowerFloor below κ)
                  (record st
                    { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                ≤-refl
        in (r , subs-shared {κ = κ} {below = below} slEq
                  (slot-connect {κ = κ} {below = below} doneEq connEq
                    (connect {κ = κ} {below = below} refl dv))) , s

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

redFnAcc f ρ rρ k ok aK a aM {v} p = redTmAcc f (v ∷ᵉ ρ) (p , rρ) k ok aK a aM

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
-- THE FLATTENER'S WALK.
------------------------------------------------------------------

-- THE GUARD, WRITTEN ONCE.  An unvouched observable is subscribed at
-- the ceiling the state actually has room for, by the candidate at
-- values with the accessibility peeled to it, under the continuation
-- dropped to it.  The `with` on the comparison is what the checker
-- reads: the yes-branch applies the accessibility's field, and the
-- no-branch is the leaf.
red-consume {u = u} mergeAllᵒ nid κ now o co rp s sched st aM rm
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      (_ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)) , s
... | just (cell-st _) =
      (_ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)) , s
... | just (take-st _) =
      (_ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)) , s
... | just (batchSync-st _ _ _) =
      (_ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)) , s
... | just (switch-st _ _) =
      (_ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)) , s
... | just (exhaust-st _ _) =
      (_ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)) , s
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u in eqw
...   | no _ =
        (_ , consume-all-nil
               (trans (cong (consumeUsable mergeAllᵒ u) eq) (cong ⌊_⌋ eqw))) , s
...   | yes refl with hasRoom lim act in eqr
...     | false = (_ , consume-all-enqueue eq eqr) , s
...     | true =
          let inst   = freshId nodeᵏ (Sched.mint sched)
              sched′ = record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }
              st′    = record st
                         { nodes = setNode nid (mergeAll-st lim (suc act) q od)
                             (EvalSt.nodes st) }
              ((( out , sched₁ , st₁) , d) , s′) =
                red-hop mergeAllᵒ nid inst κ now o co rp s sched′ st′ aM rm
          in ((out , sched₁ , st₁) , consume-all-sub eq eqr (inner refl d)) , s′

red-consume {u = u} switchᵒ nid κ now o co rp s sched st aM rm
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      (_ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq)) , s
... | just (cell-st _) =
      (_ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq)) , s
... | just (take-st _) =
      (_ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq)) , s
... | just (batchSync-st _ _ _) =
      (_ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq)) , s
... | just (mergeAll-st _ _ _ _) =
      (_ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq)) , s
... | just (exhaust-st _ _) =
      (_ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq)) , s
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (sched₁ , st₁) =
        let inst   = freshId nodeᵏ (Sched.mint sched₁)
            sched′ = record sched₁ { mint = setAt nodeᵏ (suc inst) (Sched.mint sched₁) }
            st′    = record st₁
                       { nodes = setNode nid (switch-st (just inst) od)
                           (EvalSt.nodes st₁) }
            rm′    = room-keeps (switchKill-keeps cur sched st eqk) rm
            ((( out , sched₂ , st₂) , d) , s′) =
              red-hop switchᵒ nid inst κ now o co rp s sched′ st′ aM rm′
        in ((out , sched₂ , st₂) , consume-switch-sub eq eqk refl (inner refl d)) , s′

red-consume {u = u} exhaustᵒ nid κ now o co rp s sched st aM rm
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (cell-st _) =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (take-st _) =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (batchSync-st _ _ _) =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (mergeAll-st _ _ _ _) =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (switch-st _ _) =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (exhaust-st true _) =
      (_ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq)) , s
... | just (exhaust-st false od) =
      let inst   = freshId nodeᵏ (Sched.mint sched)
          sched′ = record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }
          st′    = record st
                     { nodes = setNode nid (exhaust-st true od) (EvalSt.nodes st) }
          ((( out , sched₁ , st₁) , d) , s′) =
            red-hop exhaustᵒ nid inst κ now o co rp s sched′ st′ aM rm
      in ((out , sched₁ , st₁) , consume-exhaust-sub eq (inner refl d)) , s′

red-hop op nid inst κ now o (just ro) rp s sched st aM rm =
  ro (from-inner op nid inst ↠[ ≤-refl ] κ)
    (fromInnerWalkRP op nid inst aM ≤-refl κ rp) s now sched st rm
red-hop {m = m} op nid inst κ now o nothing rp s sched st (acc rsM) rm
  with unconn (Sched.slots sched) (EvalSt.connectedShares st) <? m
... | yes lt =
      red-val (rsM lt) (obs _) o (from-inner op nid inst ↠[ ≤-refl ] κ)
        (fromInnerWalkRP op nid inst (rsM lt) ≤-refl κ (dropRP (<⇒≤ lt) rp))
        s now sched st ≤-refl
... | no nlt = stuck-hop o (from-inner op nid inst ↠[ ≤-refl ] κ) now s sched st rm nlt

red-walk op nid κ now []       []        rp s sched st aM rm = (_ , walk-nil) , s
red-walk op nid κ now (o ∷ os) (co ∷ cs) rp s sched st aM rm =
  let ((( out₁ , sched₁ , st₁) , c) , s₁) =
        red-consume op nid κ now o co rp s sched st aM rm
      ((( out₂ , sched₂ , st₂) , w) , s₂) =
        red-walk op nid κ now os cs rp s₁ sched₁ st₁ aM
          (room-keeps (thruConsume-keeps c) rm)
  in ((out₁ ++ out₂ , sched₂ , st₂) , walk-cons c w) , s₂

fold (thruRP op nid aM h κ rp) s now vals cs fin sched st rm =
  let ((( out₁ , sched₁ , st₁) , w) , s₁) =
        red-walk op nid κ now vals cs rp s sched st aM rm
      (fin′ , sched₂ , st₂) = thruWrap op nid fin (sched₁ , st₁)
      ((( out₂ , sched₃ , st₃) , f) , s₂) =
        fold rp s₁ now [] [] fin′ sched₂ st₂
          (room-keeps (thruWrap-keeps op nid fin sched₁ st₁)
            (room-keeps (thruWalk-keeps w) rm))
  in ((out₁ ++ out₂ , sched₃ , st₃) , fold-step (step-thru-outer w) f) , s₂

fold (fromInnerRP op allNid inst aM k aQ h κ rp) s now vals cs fin sched st rm =
  let ((( out₁ , vals′ , fin′ , sched₁ , st₁) , r , cs′) , s₁) =
        innerReact! op allNid inst κ now vals cs rp s sched st fin aM k aQ rm
      ((( out₂ , sched₂ , st₂) , f) , s₂) =
        fold rp s₁ now vals′ cs′ fin′ sched₁ st₁
          (room-keeps (innerReact-keeps r) rm)
  in ((out₁ ++ out₂ , sched₂ , st₂) , fold-step (step-from-inner r) f) , s₂

fold (fromInnerRawRP op allNid inst aM h κ rp) s now vals cs fin sched st rm =
  let ((( out₁ , vals′ , fin′ , sched₁ , st₁) , r , cs′) , s₁) =
        innerReactRaw! op allNid inst κ now vals cs rp s sched st fin aM rm
      ((( out₂ , sched₂ , st₂) , f) , s₂) =
        fold rp s₁ now vals′ cs′ fin′ sched₁ st₁
          (room-keeps (innerReact-keeps r) rm)
  in ((out₁ ++ out₂ , sched₂ , st₂) , fold-step (step-from-inner r) f) , s₂

fold (fromInnerWalkRP op allNid inst aM h κ rp) s now vals cs fin sched st rm =
  let ((( out₁ , vals′ , fin′ , sched₁ , st₁) , r , cs′) , s₁) =
        innerReactWalk! op allNid inst κ now vals cs rp s sched st fin aM rm
      ((( out₂ , sched₂ , st₂) , f) , s₂) =
        fold rp s₁ now vals′ cs′ fin′ sched₁ st₁
          (room-keeps (innerReact-keeps r) rm)
  in ((out₁ ++ out₂ , sched₂ , st₂) , fold-step (step-from-inner r) f) , s₂

------------------------------------------------------------------
-- THE COMPLETION SIDE.
------------------------------------------------------------------

inner! op allNid κ now o rp s sched st aM k aQ rm =
  let inst = freshId nodeᵏ (Sched.mint sched)
      ((( out , sched′ , st′) , d) , s′) =
        red-val aM (obs _) o (from-inner op allNid inst ↠[ ≤-refl ] κ)
          (fromInnerRP op allNid inst aM k aQ ≤-refl κ rp) s now
          (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }) st rm
  in ((inst , out , sched′ , st′) , inner refl d) , s′

-- THE DRAIN'S DESCENT IS ITS FUEL, AND THE BUDGET IT HANDS EACH SPENT
-- INNER IS THE FUEL'S TAIL.  An inner that ends synchronously inside
-- its own spend re-enters this drain through its exit frame with that
-- budget, strictly under the accessibility this clause holds; the
-- room is unchanged along that edge and the checker does not need it
-- to be.
mergeAllDrain! allNid κ now []       lim act od q       rp s sched st aM aQ rm =
  (_ , drain-spent) , s
mergeAllDrain! allNid κ now (f ∷ fs) lim act od []      rp s sched st aM aQ rm =
  (_ , drain-nil) , s
mergeAllDrain! {s = u} allNid κ now (f ∷ fs) lim act od (o ∷ q) rp s sched st aM (acc rsQ) rm
  with hasRoom lim act in eqr
... | false = (_ , drain-no-room eqr) , s
... | true  =
      let ((( inst , out , sched₁ , st₁) , sb) , s₁) =
            inner! mergeAllᵒ allNid κ now o rp s sched
              (record st
                 { nodes = setNode allNid (mergeAll-st lim (suc act) q od)
                     (EvalSt.nodes st) })
              aM (length fs) (rsQ ≤-refl) rm
          (lim₂ , act₂ , q₂ , od₂) =
            drainSt u (lookupNode allNid (EvalSt.nodes st₁))
          ((( out′ , act′ , q′ , sched₂ , st₂) , d) , s₂) =
            mergeAllDrain! allNid κ now fs lim₂ act₂ od₂ q₂ rp s₁ sched₁ st₁ aM (rsQ ≤-refl)
              (room-keeps (subscribeInner-keeps sb) rm)
      in ((out ++ out′ , act′ , q′ , sched₂ , st₂) , drain-room eqr sb refl d) , s₂

-- THE MERGE'S FINISH: FOLD THE LAST VALUES, THEN DRAIN, THEN HAND THE
-- COMPLETION UP.  The queue is reconciled against the budget in the
-- three cases the header names.
innerFinish! {s = u} mergeAllᵒ allNid inst κ now vals cs rp s sched st
             (just (mergeAll-st {w} lim act q od)) aM k aQ rm with w ≟ᵗ u in eqw
... | no  _    = (_ , finish-nil (cong ⌊_⌋ eqw) , cs) , s
... | yes refl =
      let ((( outV , sched₁ , st₁) , fp) , s₁) =
            fold rp s now vals cs false sched st rm
          rm₁ = room-keeps (foldPath-keeps fp) rm
          ((( out , act′ , q′ , sched₂ , st₂) , d) , s₂) =
            finishDrain! allNid κ now lim act od q rp s₁ sched₁ st₁ aM k aQ rm₁
      in (( outV ++ out , [] , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched₂
          , record st₂
              { nodes = setNode allNid (mergeAll-st lim act′ q′ od)
                  (EvalSt.nodes st₂) })
         , finish-all-drain fp d , []) , s₂
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st
             (just (switch-st (just c) od)) aM k aQ rm with (c ≡ᵇ inst) in eqc
... | true  = (_ , finish-switch-clear eqc , cs) , s
... | false = (_ , finish-nil eqc , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st
             (just (exhaust-st act od)) aM k aQ rm = (_ , finish-exhaust-clear , cs) , s

innerFinish! mergeAllᵒ allNid inst κ now vals cs rp s sched st nothing aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (cell-st _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (take-st _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (batchSync-st _ _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (switch-st _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (exhaust-st _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st nothing aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st (just (cell-st _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st (just (take-st _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st (just (batchSync-st _ _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st (just (mergeAll-st _ _ _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st (just (exhaust-st _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! switchᵒ allNid inst κ now vals cs rp s sched st (just (switch-st nothing _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st nothing aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (cell-st _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (take-st _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (batchSync-st _ _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (mergeAll-st _ _ _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s
innerFinish! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (switch-st _ _)) aM k aQ rm = (_ , finish-nil refl , cs) , s

-- THE WALK-ORDER FINISH IS THE BUDGETED ONE WITH NO BUDGET TO SPEND.
innerFinishWalk! {s = u} mergeAllᵒ allNid inst κ now vals cs rp s sched st
             (just (mergeAll-st {w} lim act q od)) aM rm with w ≟ᵗ u in eqw
... | no  _    = (_ , finish-nil (cong ⌊_⌋ eqw) , cs) , s
... | yes refl =
      let ((( outV , sched₁ , st₁) , fp) , s₁) =
            fold rp s now vals cs false sched st rm
          rm₁ = room-keeps (foldPath-keeps fp) rm
          ((( out , act′ , q′ , sched₂ , st₂) , d) , s₂) =
            finishWalk! allNid κ now lim act od q rp s₁ sched₁ st₁ aM rm₁
      in (( outV ++ out , [] , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched₂
          , record st₂
              { nodes = setNode allNid (mergeAll-st lim act′ q′ od)
                  (EvalSt.nodes st₂) })
         , finish-all-drain fp d , []) , s₂
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st
             (just (switch-st (just c) od)) aM rm with (c ≡ᵇ inst) in eqc
... | true  = (_ , finish-switch-clear eqc , cs) , s
... | false = (_ , finish-nil eqc , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st
             (just (exhaust-st act od)) aM rm = (_ , finish-exhaust-clear , cs) , s

innerFinishWalk! mergeAllᵒ allNid inst κ now vals cs rp s sched st nothing aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (cell-st _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (take-st _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (batchSync-st _ _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (switch-st _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! mergeAllᵒ allNid inst κ now vals cs rp s sched st (just (exhaust-st _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st nothing aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st (just (cell-st _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st (just (take-st _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st (just (batchSync-st _ _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st (just (mergeAll-st _ _ _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st (just (exhaust-st _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! switchᵒ allNid inst κ now vals cs rp s sched st (just (switch-st nothing _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st nothing aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (cell-st _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (take-st _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (batchSync-st _ _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (mergeAll-st _ _ _ _)) aM rm = (_ , finish-nil refl , cs) , s
innerFinishWalk! exhaustᵒ allNid inst κ now vals cs rp s sched st (just (switch-st _ _)) aM rm = (_ , finish-nil refl , cs) , s

-- THE RAW FINISH SEEDS THE DRAIN'S BUDGET FROM THE QUEUE AS IT
-- STANDS; every other finish is the budgeted one at budget nought,
-- which none of them spends.
innerFinishRaw! {s = u} mergeAllᵒ allNid inst κ now vals cs rp s sched st
             (just (mergeAll-st {w} lim act q od)) aM rm with w ≟ᵗ u in eqw
... | no  _    = (_ , finish-nil (cong ⌊_⌋ eqw) , cs) , s
... | yes refl =
      let ((( outV , sched₁ , st₁) , fp) , s₁) =
            fold rp s now vals cs false sched st rm
          rm₁ = room-keeps (foldPath-keeps fp) rm
          ((( out , act′ , q′ , sched₂ , st₂) , d) , s₂) =
            mergeAllDrain! allNid κ now q lim (pred act) od q rp s₁ sched₁ st₁ aM
              (<-wellFounded (length q)) rm₁
      in (( outV ++ out , [] , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched₂
          , record st₂
              { nodes = setNode allNid (mergeAll-st lim act′ q′ od)
                  (EvalSt.nodes st₂) })
         , finish-all-drain fp d , []) , s₂
innerFinishRaw! op allNid inst κ now vals cs rp s sched st ns aM rm =
  innerFinish! op allNid inst κ now vals cs rp s sched st ns aM 0 (<-wellFounded 0) rm

finishDrain! allNid κ now lim act od q rp s sched st aM k aQ rm
  with length q ≟ k
... | yes refl =
      mergeAllDrain! allNid κ now q lim (pred act) od q rp s sched st aM aQ rm
... | no _ = finishPeelQ! allNid κ now lim act od q rp s sched st aM k aQ rm

finishPeelQ! allNid κ now lim act od q rp s sched st aM k (acc rsQ) rm
  with length q <? k
... | yes lt =
      mergeAllDrain! allNid κ now q lim (pred act) od q rp s sched st aM (rsQ lt) rm
... | no _ = finishPeelM! allNid κ now lim act od q rp s sched st aM rm

finishPeelM! {m = m} allNid κ now lim act od q rp s sched st (acc rsM) rm
  with unconn (Sched.slots sched) (EvalSt.connectedShares st) <? m
... | yes lt =
      mergeAllDrain! allNid κ now q lim (pred act) od q (dropRP (<⇒≤ lt) rp) s sched st
        (rsM lt) (<-wellFounded (length q)) ≤-refl
... | no nlt = stuck-finish allNid κ now s sched st lim act q od rm nlt

finishWalk! allNid κ now lim act od []      rp s sched st aM rm = (_ , drain-spent) , s
finishWalk! allNid κ now lim act od (o ∷ q) rp s sched st aM rm =
  finishPeelM! allNid κ now lim act od (o ∷ q) rp s sched st aM rm

innerReact! op allNid inst κ now vals cs rp s sched st false aM k aQ rm =
  (_ , react-false , cs) , s
innerReact! op allNid inst κ now vals cs rp s sched st true aM k aQ rm
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = (_ , react-alive eqa , cs) , s
... | false =
      let ((r , f , cs′) , s′) =
            innerFinish! op allNid inst κ now vals cs rp s sched st
              (lookupNode allNid (EvalSt.nodes st)) aM k aQ rm
      in (r , react-dead eqa f , cs′) , s′

innerReactRaw! op allNid inst κ now vals cs rp s sched st false aM rm =
  (_ , react-false , cs) , s
innerReactRaw! op allNid inst κ now vals cs rp s sched st true aM rm
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = (_ , react-alive eqa , cs) , s
... | false =
      let ((r , f , cs′) , s′) =
            innerFinishRaw! op allNid inst κ now vals cs rp s sched st
              (lookupNode allNid (EvalSt.nodes st)) aM rm
      in (r , react-dead eqa f , cs′) , s′

innerReactWalk! op allNid inst κ now vals cs rp s sched st false aM rm =
  (_ , react-false , cs) , s
innerReactWalk! op allNid inst κ now vals cs rp s sched st true aM rm
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = (_ , react-alive eqa , cs) , s
... | false =
      let ((r , f , cs′) , s′) =
            innerFinishWalk! op allNid inst κ now vals cs rp s sched st
              (lookupNode allNid (EvalSt.nodes st)) aM rm
      in (r , react-dead eqa f , cs′) , s′

------------------------------------------------------------------
-- THE RAW CONTINUATION AND THE SHARE FAN-OUT.
------------------------------------------------------------------

-- THE RAW CONTINUATION IS THE FRAME BUILDERS OVER THEMSELVES, with
-- the candidates each builder wants drawn from `red-val` at this
-- ceiling.  The root and the sink are the two base cases: the root
-- mints, the sink fans out.  The fold's builder is seeded with no held
-- cell; the flattener's with this ceiling's accessibility, so that its
-- walk's guard peels from here; the exit frame's is its raw builder.
rawRP ac le aM root = rootRP
rawRP {n = n} (acc rec) le aM (share-sink i below) =
  mkRP λ tt now vals _ fin sched st rm →
    let (r , d) = dispatchShare! (rec (monus-sink i (≤-trans le below))) below
                    now vals fin sched st aM rm
    in (r , fold-sink d) , tt
rawRP ac le aM (map-f (Θ , f , ρ) ↠[ h ] κ) =
  mapRP (Θ , f , ρ)
    (redFnAcc f ρ (red-env aM ρ) _ (ib-topᵗ f) (<-wellFounded _) (<-wellFounded (gsizeᵗ f)) aM)
    h κ (rawRP ac (≤-trans le h) aM κ)
rawRP ac le aM (scan-f (Θ , f , ρ) nid ↠[ h ] κ) =
  scanRP (Θ , f , ρ) nid
    (redFnAcc f ρ (red-env aM ρ) _ (ib-topᵗ f) (<-wellFounded _) (<-wellFounded (gsizeᵗ f)) aM)
    nothing h κ (rawRP ac (≤-trans le h) aM κ)
rawRP ac le aM (take-f nid ↠[ h ] κ) =
  takeRP nid h κ (rawRP ac (≤-trans le h) aM κ)
rawRP ac le aM (batchSync-f nid ↠[ h ] κ) =
  batchRP nid h κ (rawRP ac (≤-trans le h) aM κ)
rawRP ac le aM (from-inner op allNid inst ↠[ h ] κ) =
  fromInnerRawRP op allNid inst aM h κ (rawRP ac (≤-trans le h) aM κ)
rawRP ac le aM (thru-outer op nid ↠[ h ] κ) =
  thruRP op nid aM h κ (rawRP ac (≤-trans le h) aM κ)

dispatchShare! {i = i} ac below now vals fin sched st aM rm =
  let (_ , w) = shareWalk! ac now vals fin sched (shareDying i fin st) aM
                  (room-keeps (shareDying-keeps i fin sched st) rm)
  in _ , disp w

shareWalk! ac now [] false sched st aM rm = _ , walk-nil
shareWalk! {i = i} ac now [] true sched st aM rm =
  let (_ , g) = shareGo! ac now [] true
                  (shareAdmit i (EvalSt.registry st)) sched (shareSpend i st) aM
                  (room-keeps (shareSpend-keeps i sched st) rm)
  in _ , walk-end g
shareWalk! {i = i} ac now (v ∷ vs) fin sched₀ st₀ aM rm =
  let ((emits , sched₁ , st₁) , g) =
        shareGo! ac now (v ∷ []) false
          (shareAdmit i (EvalSt.registry st₀)) sched₀ st₀ aM rm
      (_ , r) = shareWalk! ac now vs fin sched₁ st₁ aM
                  (room-keeps (shareGo-keeps g) rm)
  in _ , walk-more g r

-- EVERY ADMITTED CHAIN IS WALKED RAW, at this ceiling, from the floor
-- the registry row names.
shareGo! ac now vals fin [] sched st aM rm = _ , go-nil
shareGo! {i = i} ac now vals fin ((rid , p) ∷ ps) sched st aM rm
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (_ , g) = shareGo! ac now vals fin ps sched st aM rm
              in _ , go-cut eqc g
... | false =
      let ((( emits , sched₁ , st₁) , f) , _) =
            fold (rawRP ac ≤-refl aM p) tt now vals (vouchAll _ vals) fin sched
              (record st { delivered = rid ∷ EvalSt.delivered st }) rm
          (_ , g) = shareGo! ac now vals fin ps sched₁ st₁ aM
                      (room-keeps (foldPath-keeps f) rm)
      in _ , go-live eqc f g
