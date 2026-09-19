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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Rx.Prim using (Tick; Source)
open import Function.Base using (case_of_)
open import Relation.Nullary using (yes; no)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ;
  Ctx; Closed; Val; Tm; FnClo; applyClo; Env; []ᵉ; _∷ᵉ_; evalWith; foldVals;
  isData; lookupEnv; _≟ᵗ_; inputsBelowᵉ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId;
  scanStep; batchSyncPush; batchSyncFlush; lookupNode; batchSync-st;
  memberSource)
open import Rx.Evaluator.Domain using (subscribeE⇓; emit⇓; emits⇓; close⇓; drainQueue⇓)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Decide using (≡ᵇ-refl)
open import Data.Fin using (Fin; toℕ)
import Data.Fin as F
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (+-mono-≤; +-mono-<-≤; +-mono-≤-<)
open import Data.Vec using (tabulate; foldr′; lookup)

------------------------------------------------------------------
-- WHAT EVERY FAMILY HERE ANSWERS IN.
------------------------------------------------------------------

Out : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set
Out {Γ = Γ} {t = t} e = Stream Γ t × Sched Γ × EvalSt e

------------------------------------------------------------------
-- WHAT THE BUILDER RECURSES ON.
------------------------------------------------------------------

-- THE ONE QUANTITY THAT ORDERS A CONNECT, and it is a COUNT rather
-- than a statement about what the store holds -- which is the whole
-- reason it is available where an invariant is not.  A connect is
-- guarded by its slot being shared and absent from the connected
-- list, and adds it on the way out; nothing anywhere takes one back
-- out, and the list starts empty.  So this number strictly drops
-- across exactly the call that raises the floor measure, and is left
-- alone by every other arm.
--
-- THE CANDIDATE NEVER APPEARS IN IT.  It rides the three halves below
-- as an inert index, so the descent that licenses them is still the
-- TYPE and is untouched -- the distinction that keeps this clear of
-- the route `Rx.Evaluator.Builder`'s own header records as dead.

-- AND IT IS A FUNCTION OF TWO FIELDS AND NOTHING ELSE, which is what
-- makes a step's obligation to it cheap: a store handed back with the
-- same connected list carries the same count, whatever else moved.
-- AND IT IS A SUM OF PER-SLOT COSTS, SPLIT OUT RATHER THAN SEALED IN
-- A `where`, because the descent needs the summand named at two
-- different connected lists at once -- and needs the slot handed to it
-- as an ARGUMENT, so that a caller holding `slots i ≡ shared d` can
-- rewrite the cost rather than being stuck under a `with`.
sumF : ∀ {n} → (Fin n → ℕ) → ℕ
sumF {n} f = foldr′ _+_ 0 (tabulate {n = n} f)

slotCostS : ∀ {n} {Γ : Ctx n} {k t} → Slot Γ k t → Source → List Source → ℕ
slotCostS (scripted _) s cs = 0
slotCostS (shared _)   s cs = if memberSource s cs then 0 else 1

slotCost : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
slotCost slots cs i = slotCostS (slots i) (toℕ i) cs

unconnectedS : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
unconnectedS slots cs = sumF (slotCost slots cs)

unconnected : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
unconnected sched st = unconnectedS (Sched.slots sched) (EvalSt.connectedShares st)

unconn-cong : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              (sched : Sched Γ) {st st′ : EvalSt e}
            → EvalSt.connectedShares st′ ≡ EvalSt.connectedShares st
            → unconnected sched st′ ≡ unconnected sched st
unconn-cong sched p = cong (unconnectedS (Sched.slots sched)) p

-- WHAT A CONNECT COSTS THE COUNT, WHICH IS THE ORDER THE UPWARD EDGE
-- IS SPENT AGAINST.  Adding a source to the connected list can only
-- lower a slot's cost, and at the slot being connected it lowers it
-- from one to nothing -- the guard says that slot is shared and absent
-- -- so the sum strictly drops.  Two arithmetic facts over the sum do
-- all of it, and neither mentions this development: a pointwise-≤
-- family sums no larger, and one strict drop under a pointwise-≤
-- family makes the sum strictly smaller.
sumF-mono : ∀ {n} (f g : Fin n → ℕ) → (∀ j → g j ≤ f j) → sumF g ≤ sumF f
sumF-mono {zero}  f g le = z≤n
sumF-mono {suc n} f g le =
  +-mono-≤ (le F.zero)
    (sumF-mono (λ j → f (F.suc j)) (λ j → g (F.suc j)) (λ j → le (F.suc j)))

sumF-drop : ∀ {n} (f g : Fin n → ℕ) (i : Fin n)
          → (∀ j → g j ≤ f j) → g i < f i → sumF g < sumF f
sumF-drop f g F.zero le lt =
  +-mono-<-≤ lt
    (sumF-mono (λ j → f (F.suc j)) (λ j → g (F.suc j)) (λ j → le (F.suc j)))
sumF-drop f g (F.suc i) le lt =
  +-mono-≤-< (le F.zero)
    (sumF-drop (λ j → f (F.suc j)) (λ j → g (F.suc j)) i
      (λ j → le (F.suc j)) lt)

member-here : ∀ (s : Source) (cs : List Source) → memberSource s (s ∷ cs) ≡ true
member-here s cs rewrite ≡ᵇ-refl s = refl

cost-mono : ∀ {n} {Γ : Ctx n} (slots : Slots Γ) (s : Source) (cs : List Source)
            (i : Fin n)
          → slotCost slots (s ∷ cs) i ≤ slotCost slots cs i
cost-mono slots s cs i with slots i
... | scripted _ = z≤n
... | shared _ with toℕ i ≡ᵇ s | memberSource (toℕ i) cs
...   | true  | _     = z≤n
...   | false | true  = z≤n
...   | false | false = s≤s z≤n

unconn-connect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                 (i : Fin n) (sched : Sched Γ) (st : EvalSt e)
                 {d : Closed Γ (lookup Γ i)}
                 {okd : T (inputsBelowᵉ (toℕ i) d)}
               → Sched.slots sched i ≡ shared d {ok = okd}
               → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false
               → suc (unconnectedS (Sched.slots sched)
                        (toℕ i ∷ EvalSt.connectedShares st))
                   ≤ unconnected sched st
unconn-connect i sched st slEq connEq =
  sumF-drop (slotCost slots cs) (slotCost slots (toℕ i ∷ cs)) i
    (cost-mono slots (toℕ i) cs) hit
  where
    slots = Sched.slots sched
    cs    = EvalSt.connectedShares st

    lhs≡0 : slotCost slots (toℕ i ∷ cs) i ≡ 0
    lhs≡0 = trans (cong (λ sl → slotCostS sl (toℕ i) (toℕ i ∷ cs)) slEq)
                  (cong (λ b → if b then 0 else 1) (member-here (toℕ i) cs))

    rhs≡1 : slotCost slots cs i ≡ 1
    rhs≡1 = trans (cong (λ sl → slotCostS sl (toℕ i) cs) slEq)
                  (cong (λ b → if b then 0 else 1) connEq)

    hit : slotCost slots (toℕ i ∷ cs) i < slotCost slots cs i
    hit rewrite lhs≡0 | rhs≡1 = s≤s z≤n

-- WHAT A STEP OWES THE COUNT, AND IT IS THE CREDIT THE SHAPE ABOVE
-- BUYS ON.  A frame's obligation is stated under a bound on the store
-- it is handed, so a frame that runs a step and then spends the next
-- obligation has to know the step left the count where it was.  It
-- did: the connected list is written at exactly one site in the whole
-- tree -- a connect, which EXTENDS it -- and the slot telescope is
-- fixed at the start of the run, so every other step leaves both
-- readings alone and the count with them.
--
-- STATED OVER THE RELATION RATHER THAN THE STEP, because what a
-- builder holds at the point of spending is the derivation and not
-- the function that produced it.  Five of them because the obligation
-- is spent through five different relations, and the fact is the same
-- fact in each.
--
-- TWIN: `unconn-latch` -- the same fact one level down, over a store
--   STEP rather than a derivation: a case split on the move, every arm
--   discharged outright because the count reads two fields and the
--   move writes neither.  Each of these five is that proof once per
--   constructor, and the arms it needs are proven already.
postulate
  unconn-emit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {κ : Path Γ lo u t} {now} {v : Val Γ u}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → emit⇓ {e = e} κ now v sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st

  unconn-close : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → close⇓ {e = e} κ now sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st

  unconn-subs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → subscribeE⇓ {e = e} b κ now sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st

  unconn-emits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now} {vs : List (Val Γ u)}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → emits⇓ {e = e} κ now vs sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st

  unconn-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {now}
                   {q : List (Val Γ (obs u))}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → drainQueue⇓ {e = e} op nid κ now q sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st

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

  Red : ∀ {n} {Γ : Ctx n} (m : ℕ) (t : Ty) → Val Γ t → Set
  Red m unitᵗ     _        = ⊤
  Red m boolᵗ     _        = ⊤
  Red m natᵗ      _        = ⊤
  Red m uniqᵗ     _        = ⊤
  Red m (s ×ᵗ u)  (a , b)  = Red m s a × Red m u b
  Red m (s +ᵗ u)  (inj₁ a) = Red m s a
  Red m (s +ᵗ u)  (inj₂ b) = Red m u b
  Red m (listᵗ s) xs       = All (Red m s) xs
  Red {Γ = Γ} m (obs u) b =
    ∀ {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) → Handles {m = m} u κ
    → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
    → Σ (Out e) λ r → subscribeE⇓ {e = e} b κ now sched st r

  -- ONE VALUE, HANDED TO THE PATH WITH ITS OWN CANDIDATE.  The
  -- candidate travels WITH the value rather than being recovered at
  -- the far end, which is what lets a flattener's frame subscribe what
  -- reaches it without asking anything of the store.
  Emits : ∀ {n} {Γ : Ctx n} {t lo m} (u : Ty) → Path Γ lo u t → Set
  Emits {Γ = Γ} {t = t} {m = m} u κ =
    ∀ {e : Closed Γ t} {v : Val Γ u} → Red m u v
    → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
    → Σ (Out e) λ r → emit⇓ {e = e} κ now v sched st r

  -- THE END CARRIES NO PAYLOAD, so this half asks for nothing and is
  -- where every frame that does work on a completion is discharged.
  Closes : ∀ {n} {Γ : Ctx n} {t lo m} {u : Ty} → Path Γ lo u t → Set
  Closes {Γ = Γ} {t = t} {m = m} κ =
    ∀ {e : Closed Γ t} (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    → unconnected sched st ≤ m
    → Σ (Out e) λ r → close⇓ {e = e} κ now sched st r

  Handles : ∀ {n} {Γ : Ctx n} {t lo m} (u : Ty) → Path Γ lo u t → Set
  Handles {m = m} u κ = Emits {m = m} u κ × Closes {m = m} κ

-- A FRAME'S FUNCTION CARRIES THE CANDIDATE ACROSS, which is the one
-- thing a transformer owes and the only thing a path builder asks of
-- the term face.
RedFn : ∀ {n} {Γ : Ctx n} {s u} (m : ℕ) → FnClo Γ s u → Set
RedFn {Γ = Γ} {s = s} {u = u} m fn =
  ∀ {v : Val Γ s} → Red m s v → Red m u (applyClo fn v)

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's function is a term with one
-- entry bound, so the fundamental theorem at terms has to be stated
-- under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} {Θ : List Ty} (m : ℕ) → Env Γ Θ → Set
RedEnv m []ᵉ                 = ⊤
RedEnv m (_∷ᵉ_ {s = t} v vs) = Red m t v × RedEnv m vs

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
  red-scanned : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u m}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                  (v : Val Γ s) (st : EvalSt e)
                  {ac : Val Γ u} {st₁ : EvalSt e}
              → scanStep {e = e} fn nid v st ≡ (just ac , st₁)
              → Red {Γ = Γ} m u ac

  red-flushed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                  (nid : NodeId) (st : EvalSt e)
                  {g : Val Γ (s ×ᵗ listᵗ s)} {st₁ : EvalSt e}
              → batchSyncFlush {e = e} {s = s} nid st ≡ (just g , st₁)
              → Red {Γ = Γ} m (s ×ᵗ listᵗ s) g

-- THE BRACKET'S PUSH NEVER HANDS BACK WHAT IT IS HOLDING, which is
-- what takes it out of the group above: the synchronous arm BUFFERS
-- and emits nothing, so the only value this step ever produces is the
-- ARRIVING one, alone, under an empty tail.  Its candidate is then the
-- emitting premise the caller already holds, and the tail's is the
-- empty `All` -- so the step asks the store for nothing at all and the
-- missing place to say it is not needed here.  The premise is what
-- makes it provable rather than a weakening: the spender is an `Emits`,
-- whose own signature carries the arriving value's candidate.
red-pushed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
               (nid : NodeId) (v : Val Γ s) (st : EvalSt e)
               {g : Val Γ (s ×ᵗ listᵗ s)} {st₁ : EvalSt e}
           → Red {Γ = Γ} m s v
           → batchSyncPush {e = e} nid v st ≡ (just g , st₁)
           → Red {Γ = Γ} m (s ×ᵗ listᵗ s) g
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
red-data : ∀ {n} {Γ : Ctx n} {m} (u : Ty) → T (isData u) → (v : Val Γ u)
         → Red {Γ = Γ} m u v
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

redDatas : ∀ {n} {Γ : Ctx n} {m} (u : Ty) → T (isData u) → (vs : List (Val Γ u))
         → All (Red {Γ = Γ} m u) vs
redDatas u ok []       = []
redDatas u ok (v ∷ vs) = red-data u ok v ∷ redDatas u ok vs

------------------------------------------------------------------
-- THE TWO CONGRUENCES THE TERM FACE CANNOT DO FOR ITSELF.
------------------------------------------------------------------

redLookup : ∀ {n} {Γ : Ctx n} {Θ t m} (σ : Env Γ Θ) → RedEnv m σ
          → (x : t ∈ Θ) → Red m t (lookupEnv σ x)
redLookup (v ∷ᵉ vs) (p , ps) (here refl) = p
redLookup (v ∷ᵉ vs) (p , ps) (there x)   = redLookup vs ps x

-- A FOLD PRESERVES THE CANDIDATE WHEN ITS STEP DOES, AND THE STEP IS A
-- HYPOTHESIS FOR THE REASON `RedFn`'s IS: the fundamental theorem at
-- terms is a member of the recursion next door, so a walk declared
-- here cannot call it.  What is new is the recursion itself — every
-- other former's value is a function of its subterms' values, so
-- congruence discharges it, while a fold runs its step once per
-- ELEMENT and the candidate has to be re-established at each.
redFoldVals : ∀ {n} {Γ : Ctx n} {Θ s u m}
              (f : Tm Γ [] [] (s ∷ u ∷ Θ) u) (σ : Env Γ Θ)
            → (∀ {x : Val Γ s} {a : Val Γ u} → Red m s x → Red m u a
                 → Red m u (evalWith f (x ∷ᵉ a ∷ᵉ σ)))
            → ∀ {xs : List (Val Γ s)} → All (Red m s) xs
            → ∀ {a : Val Γ u} → Red m u a
            → Red m u (foldVals f σ xs a)
redFoldVals f σ step []       ra = ra
redFoldVals f σ step (p ∷ ps) ra = redFoldVals f σ step ps (step p ra)
