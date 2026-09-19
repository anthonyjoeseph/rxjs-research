------------------------------------------------------------------
-- REDUCIBILITY: THE DESCENT THE TYPE FUNDS, WHERE THE RANK STOOD.
------------------------------------------------------------------

-- WHY IT IS A FUNCTION AND NOT A FAMILY.  A relation relating an
-- observable to its subscriptions would have to be introduced by a
-- constructor per former, and the whole point of the candidate is that
-- the observable arm is a PROMISE about every path rather than a fact
-- about a shape.  A function into `Set`, recursing on the type, says
-- exactly that and nothing else.
--
-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- is indexed by the store, so a candidate that constrained the store
-- would be a predicate over a record whose own index mentions the
-- candidate.  Quantifying is what keeps the two apart, and it costs
-- nothing at the call sites: every one of them has a concrete state in
-- hand.
--
-- AND WHAT A PER-VALUE MACHINE CHANGED IS WHERE THE PROMISE POINTS.
-- While a subscribe handed back a burst at the SOURCE's element type,
-- the candidate could carry a second conjunct saying every value in
-- that burst was itself reducible — one type smaller, which is the
-- whole of the descent.  A subscribe now emits at the ROOT type and
-- returns nothing a consumer can read, so the conjunct has nowhere to
-- live.  What replaces it is `Handles`: the CONTINUATION is what must
-- be able to absorb a reducible value, and a continuation at element
-- type `u` mentions the candidate only at `u`.  Same descent, stated
-- over the path instead of over the output.
module Rx.Evaluator.Reducible where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick)
open import Function.Base using (case_of_)
open import Relation.Nullary using (yes; no)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ;
  Ctx; Closed; Val; Tm; FnClo; applyClo; Env; []ᵉ; _∷ᵉ_; evalWith; foldVals;
  isData; lookupEnv; _≟ᵗ_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; NodeId;
  scanStep; batchSyncPush; batchSyncFlush; lookupNode; batchSync-st)
open import Rx.Evaluator.Domain using (subscribeE⇓; emit⇓; close⇓)

------------------------------------------------------------------
-- WHAT EVERY FAMILY HERE ANSWERS IN.
------------------------------------------------------------------

Out : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set
Out {Γ = Γ} {t = t} e = Stream Γ t × Sched Γ × EvalSt e

------------------------------------------------------------------
-- THE CANDIDATE.
------------------------------------------------------------------

-- AT A DATA TYPE IT IS TRIVIAL, because nothing about a number can
-- fail to be subscribable, and at `obs` it is the promise the whole
-- development spends: this value can be subscribed under ANY
-- continuation that knows what to do with what it produces.
--
-- THE THREE HALVES ARE ONE BLOCK BECAUSE THE PROMISE MENTIONS THEM
-- AND THEY MENTION IT BACK, AND THE DESCENT IS THE TYPE.  `Red` at
-- `obs u` reaches `Handles` at `u`, which reaches `Emits` at `u`,
-- which reaches `Red` at `u` — strictly smaller than the `obs u` it
-- started from, and nothing in the chain grows.  That is the one
-- property the shape has to have, and it is why the continuation's
-- obligation is stated at the ELEMENT type rather than as a
-- conjunction over the path's frames: a frame's output type is
-- unrelated to its input's, so a per-frame statement would reach the
-- candidate at a type the recursion cannot order.
mutual

  Red : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → Set
  Red unitᵗ     _        = ⊤
  Red boolᵗ     _        = ⊤
  Red natᵗ      _        = ⊤
  Red uniqᵗ     _        = ⊤
  Red (s ×ᵗ u)  (a , b)  = Red s a × Red u b
  Red (s +ᵗ u)  (inj₁ a) = Red s a
  Red (s +ᵗ u)  (inj₂ b) = Red u b
  Red (listᵗ s) xs       = All (Red s) xs
  Red {Γ = Γ} (obs u) b =
    ∀ {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) → Handles u κ
    → (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    → Σ (Out e) λ r → subscribeE⇓ {e = e} b κ now sched st r

  -- ONE VALUE, HANDED TO THE PATH WITH ITS OWN CANDIDATE.  The
  -- candidate travels WITH the value rather than being recovered at
  -- the far end, which is what lets a flattener's frame subscribe what
  -- reaches it without asking anything of the store.
  Emits : ∀ {n} {Γ : Ctx n} {t lo} (u : Ty) → Path Γ lo u t → Set
  Emits {Γ = Γ} {t = t} u κ =
    ∀ {e : Closed Γ t} {v : Val Γ u} → Red u v
    → (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    → Σ (Out e) λ r → emit⇓ {e = e} κ now v sched st r

  -- THE END CARRIES NO PAYLOAD, so this half asks for nothing and is
  -- where every frame that does work on a completion is discharged.
  Closes : ∀ {n} {Γ : Ctx n} {t lo} {u : Ty} → Path Γ lo u t → Set
  Closes {Γ = Γ} {t = t} κ =
    ∀ {e : Closed Γ t} (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    → Σ (Out e) λ r → close⇓ {e = e} κ now sched st r

  Handles : ∀ {n} {Γ : Ctx n} {t lo} (u : Ty) → Path Γ lo u t → Set
  Handles u κ = Emits u κ × Closes κ

-- A FRAME'S FUNCTION CARRIES THE CANDIDATE ACROSS, which is the one
-- thing a transformer owes and the only thing a path builder asks of
-- the term face.
RedFn : ∀ {n} {Γ : Ctx n} {s u} → FnClo Γ s u → Set
RedFn {Γ = Γ} {s = s} {u = u} fn =
  ∀ {v : Val Γ s} → Red s v → Red u (applyClo fn v)

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's function is a term with one
-- entry bound, so the fundamental theorem at terms has to be stated
-- under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} {Θ : List Ty} → Env Γ Θ → Set
RedEnv []ᵉ                   = ⊤
RedEnv (_∷ᵉ_ {s = t} v vs)   = Red t v × RedEnv vs

------------------------------------------------------------------
-- WHAT THE MACHINE HANDS BACK, AND WHY IT IS NOT PROVEN HERE.
------------------------------------------------------------------

-- TWO STEPS HAND A VALUE BACK OUT OF THE STORE, AND A VALUE TAKEN
-- OUT OF ONE ARRIVES WITHOUT THE CANDIDATE IT WENT IN WITH.  The
-- fold's accumulator and the bracket's flushed group are each written
-- by a clause that HAD the candidate -- the arriving value's own --
-- and read by a clause that has only the store.  Both are TRUE, and
-- trivially so: a value at observable type is a closure over a term,
-- and the term face proves the candidate of every such closure.  What
-- is missing is a place to say it.
--
-- AND THE ROUTE THROUGH THE TERM FACE IS WHAT CLOSES RATHER THAN WHAT
-- OPENS.  The fundamental theorem at VALUES is total, so it discharges
-- both on paper -- but the walk that spends them is the same walk
-- the term face re-enters when it connects a share, so calling it here
-- is a cycle and not a proof.  That is why the statements sit at the
-- STEP and not at the node: what the spender has in hand is the step's
-- own equation, so a leaf stated there costs its call site one
-- application and nothing else.
--
-- DEAD ROUTE: an invariant on the STATE, threaded through the
--   builders and re-established at each write.  It is not an import
--   cycle but a DEFINITIONAL one, and it does not resolve by cutting
--   the modules differently: the candidate's observable arm quantifies
--   over every state, so an invariant naming the candidate cannot be a
--   premise of that arm -- and `Handles`, which is a premise of it,
--   would then have to carry the invariant too.  The recursion does
--   not order it either: the arm descends on the ELEMENT type, while a
--   predicate over a store reaches the candidate at whatever type a
--   node happens to hold, which is unrelated to it.  Parameterising
--   the state record over an abstract node predicate is the same cycle
--   DEFERRED -- the instantiation ties the knot, and the executable
--   face pays a threaded parameter it only ever meets at the trivial
--   predicate.  And a SYNTACTIC invariant saying a stored value is the
--   denotation of a closed term is VACUOUS: reflection is total, so
--   every value is one and the pairing carries no information.
-- DEAD ROUTE: making the candidate an inductive FAMILY, so that strict
--   positivity licenses what the type descent will not.  The descent is
--   what the function form spends and a store notion is exactly what
--   breaks it, so the family is the only other licence on offer -- and
--   it is already spent.  `Handles` is a PREMISE of the observable arm
--   and the candidate is a premise of `Handles`, so the candidate sits
--   to the left of an arrow inside its own definition however the store
--   is added; a doubly negative occurrence is positive but not STRICTLY
--   positive, which is the one Agda accepts.  All three forms were put
--   to the checker at minimal scale and all three are refused: the
--   family for positivity, the function for termination, and the
--   genuinely inductive-recursive shape -- store predicate as data,
--   candidate as function -- for positivity again.  The licence this
--   route needs exists in neither checker.
postulate
  red-scanned : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                  (v : Val Γ s) (st : EvalSt e)
                  {ac : Val Γ u} {st₁ : EvalSt e}
              → scanStep {e = e} fn nid v st ≡ (just ac , st₁)
              → Red {Γ = Γ} u ac

  red-flushed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                  (nid : NodeId) (st : EvalSt e)
                  {g : Val Γ (s ×ᵗ listᵗ s)} {st₁ : EvalSt e}
              → batchSyncFlush {e = e} {s = s} nid st ≡ (just g , st₁)
              → Red {Γ = Γ} (s ×ᵗ listᵗ s) g

-- THE BRACKET'S PUSH NEVER HANDS BACK WHAT IT IS HOLDING, which is
-- what takes it out of the group above: the synchronous arm BUFFERS
-- and emits nothing, so the only value this step ever produces is the
-- ARRIVING one, alone, under an empty tail.  Its candidate is then the
-- emitting premise the caller already holds, and the tail's is the
-- empty `All` -- so the step asks the store for nothing at all and the
-- missing place to say it is not needed here.  The premise is what
-- makes it provable rather than a weakening: the spender is an `Emits`,
-- whose own signature carries the arriving value's candidate.
red-pushed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
               (nid : NodeId) (v : Val Γ s) (st : EvalSt e)
               {g : Val Γ (s ×ᵗ listᵗ s)} {st₁ : EvalSt e}
           → Red {Γ = Γ} s v
           → batchSyncPush {e = e} nid v st ≡ (just g , st₁)
           → Red {Γ = Γ} (s ×ᵗ listᵗ s) g
red-pushed {s = s} nid v st rv eq with lookupNode nid (EvalSt.nodes st)
red-pushed nid v st rv refl | just (batchSync-st false _) = rv , []
red-pushed {s = s} nid v st rv eq | just (batchSync-st {w} true buf)
  with w ≟ᵗ s
red-pushed nid v st rv eq | just (batchSync-st true buf) | no  _    =
  case eq of λ ()
red-pushed nid v st rv eq | just (batchSync-st true buf) | yes refl =
  case eq of λ ()

------------------------------------------------------------------
-- THE TRIVIAL CLOSURES, WHICH ARE WHAT THE SCRIPTED SOURCES SPEND.
------------------------------------------------------------------

-- THE PRODUCT AND SUM ARMS OF `isData` GUARD ON THE LEFT FACTOR, so
-- the witness has to be taken apart before either side can be used.
T-if : ∀ (b c : Bool) → T (if b then c else false) → T b × T c
T-if true  c ok = tt , ok
T-if false c ()

-- EVERY VALUE OF A DATA TYPE IS REDUCIBLE, AND THAT IS WHY THE SLOT
-- ARM IS SHORT.  The candidate is trivial at each data former and
-- uninhabitable at `obs`, so the recursion here is the same one `Red`
-- itself runs -- it just has to be SAID, because a slot's element type
-- is `lookup Γ i` and no reduction fires on a neutral index.  What
-- carries it is the side condition every scripted slot already holds.
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

------------------------------------------------------------------
-- THE TWO CONGRUENCES THE TERM FACE CANNOT DO FOR ITSELF.
------------------------------------------------------------------

redLookup : ∀ {n} {Γ : Ctx n} {Θ t} (σ : Env Γ Θ) → RedEnv σ
          → (x : t ∈ Θ) → Red t (lookupEnv σ x)
redLookup (v ∷ᵉ vs) (p , ps) (here refl) = p
redLookup (v ∷ᵉ vs) (p , ps) (there x)   = redLookup vs ps x

-- A FOLD PRESERVES THE CANDIDATE WHEN ITS STEP DOES, AND THE STEP IS A
-- HYPOTHESIS FOR THE REASON `RedFn`'s IS: the fundamental theorem at
-- terms is a member of the recursion next door, so a walk declared
-- here cannot call it.  What is new is the recursion itself — every
-- other former's value is a function of its subterms' values, so
-- congruence discharges it, while a fold runs its step once per
-- ELEMENT and the candidate has to be re-established at each.
redFoldVals : ∀ {n} {Γ : Ctx n} {Θ s u}
              (f : Tm Γ [] [] (s ∷ u ∷ Θ) u) (σ : Env Γ Θ)
            → (∀ {x : Val Γ s} {a : Val Γ u} → Red s x → Red u a
                 → Red u (evalWith f (x ∷ᵉ a ∷ᵉ σ)))
            → ∀ {xs : List (Val Γ s)} → All (Red s) xs
            → ∀ {a : Val Γ u} → Red u a
            → Red u (foldVals f σ xs a)
redFoldVals f σ step []       ra = ra
redFoldVals f σ step (p ∷ ps) ra = redFoldVals f σ step ps (step p ra)
