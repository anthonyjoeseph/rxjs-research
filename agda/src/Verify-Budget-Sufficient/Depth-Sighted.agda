-- THE SUBSCRIBE-SIDE CEILING, and the induction that carries it.  The
-- statement is one file's worth of subject matter: a descent measured
-- against what the subscribing state can see.  Its shape, what is
-- traded at each edge and what the size factor buys are argued at the
-- assembly below; the leaves above it are the clauses that argument
-- does not close.
module Verify-Budget-Sufficient.Depth-Sighted where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; ⊔-lub; +-assoc; +-comm;
  *-mono-≤; *-monoˡ-≤; ^-monoʳ-≤; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; m≤n+m; m≤m+n; n≤1+n; m⊔n≤m+n;
  *-distribˡ-+; +-identityʳ; +-suc; <ᵇ⇒<)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import Data.Bool using (Bool; T; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; trans; sym; refl; subst)

open import Rx.Exp using (Ctx; Closed; Fn; Val; obs; sizeᵉ; syncSizeᵉ; syncSizeᵗ; evalTm; unfoldμ; ofᵉ; emptyᵉ; deferᵉ;
  μᵉ; varᵉ; input; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; inputsBelowᵉ;
  inputsBelowᵗ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Inputs-Below using (ib-unfoldμ)
open import Decide using (∧ʳ)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; InstEmit)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; Stream; map-f; take-f; _↠_; subscribeE;
  mintNode; installNode; register; take-st; scan-st; scan-f; share-sink; thru-outer;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; stepFrame; splitEvents; NodeId; thruConsume)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵛ)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthBurst; depthAll; depthFrame)
open import Verify-Budget-Sufficient.Measures using (syncSize-unfoldμ)
open import Verify-Budget-Sufficient.Nest-Subst using (nestD-unfoldμ; evalTm-nest-sync)
open import Verify-Budget-Sufficient.Nest-Walk using
  (pushFitOK; thruFitOK; nestDᵛˢ; nodesMax; nodeNestAt)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (thruConsume-slots; stepFrame-slots; subscribeE-slots)
open import Verify-Budget-Sufficient.Nest-Store using
  (pathNestD; sightCeil; sightCeil-mono; sightCeil-sum; storeNestMax;
   storeNestMax-install; storeNestMax-register; nestUnit; nodeNest;
   allFresh; allFresh-nest;
   slotWrap; slotWrapSum; slotWrap≤sum)

-- WHAT THE SUBSCRIBING STATE CAN SEE, named once so the clauses below
-- read as the trade rather than as four arguments.
--
-- THE TRADED SUM IS SCALED, by the SUBJECT's sync size, and the choice
-- of which sync size is what makes the induction go through.  It is
-- scaled at all because the two clauses that BUILD a value -- a scan's
-- seed and a map frame's payload -- pay for what they build once per
-- OCCURRENCE of the syntax that builds it, which is the shape this
-- tree proves and the shape an additive charge is refuted at; a
-- summand of slack cannot meet a factor, and a scaled summand can.
--
-- AND THE SUBJECT'S IS THE ONE THAT MOVES THE RIGHT WAY.  Every
-- structural descent shrinks the sync size while the traded sum stays
-- put, so each clause gets its exponent for free and the spare factor
-- the built value needs is exactly the head's own `suc`.  Reading the
-- PROGRAM's sync size instead would leave the exponent constant along
-- the walk -- tidier at each edge, and then no clause has any room at
-- all, since nothing relates a subterm's sync size to the program's
-- without an invariant the statement does not carry.
Sight : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  ℕ → Closed Γ u → Path Γ u t → Sched Γ → EvalSt e → ℕ
Sight {e = e} k b κ sched st =
  sightCeil (sizeᵉ e) (2 ^ syncSizeᵉ b * (pathNestD κ + nestDᵉ b)
                        + k * slotWrapSum (Sched.slots sched))
            (storeNestMax sched st) (nestUnit e (Sched.slots sched))

-- A CHAIN FRAME COSTS THE BURST NOTHING, and the three heads that mint a
-- node are chain frames.  A `map`, a `scan` and a `take` transform in
-- place: they push no story, so `depthFrame` is flatly zero at each of
-- them, and a burst is a fold of `depthFrame` over the emitted stream
-- with the state threaded through.  The threading is why this is an
-- induction rather than a computation -- every element is read at a
-- state the one before it produced -- and it is why the hypothesis
-- quantifies over the state rather than fixing it.
burst-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (bid : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t) →
  (∀ (vals : List (Val Γ s)) (fin : Bool) (sch : Sched Γ) (sto : EvalSt e) →
     depthFrame g bid now f κ vals fin sch sto ≡ 0) →
  ∀ (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst g bid now f κ ems sched st ≡ 0
burst-flat g bid now f κ h []         sched st = refl
burst-flat g bid now f κ h (em ∷ ems) sched st =
  cong₂ _⊔_ (h _ _ sched st) (burst-flat g bid now f κ h ems _ _)

-- AND WHEN THE FRAME IS NOT FLAT, THE FOLD GOES THROUGH ON AN
-- INVARIANT OVER THE REMAINING STREAM, which is what a burst needs and
-- what rules out the tidier decomposition.  A `⊔`-fold is bounded by a
-- bound on each element, so the only real content is that the element
-- bound survives the threading -- and it cannot be asked for at an
-- ARBITRARY value list, since a frame that subscribes is handed the
-- inner it subscribes and nothing outside the stream bounds that.  So
-- the predicate reads the stream as well as the state, and the second
-- premise is that one element's step carries it to the tail.  Both are
-- parameters because choosing them IS the design: a fold wants a fixed
-- ceiling rather than a per-step growth law, so what goes in here is a
-- bound and never an increment.
burst-le : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (C : ℕ)
  (g : Gas) (bid : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (P : Stream Γ s → Sched Γ → EvalSt e → Set) →
  (∀ (em : InstEmit (Val Γ s)) (ems : Stream Γ s)
     (sch : Sched Γ) (sto : EvalSt e) → P (em ∷ ems) sch sto →
     depthFrame g bid now f κ
       (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em)))
       (proj₂ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em))))
       sch sto ≤ C) →
  (∀ (em : InstEmit (Val Γ s)) (ems : Stream Γ s)
     (sch : Sched Γ) (sto : EvalSt e) → P (em ∷ ems) sch sto →
     P ems
       (proj₁ (proj₂ (proj₂ (proj₂
         (stepFrame g bid now f κ
           (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em)))
           (proj₂ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em))))
           sch sto)))))
       (proj₂ (proj₂ (proj₂ (proj₂
         (stepFrame g bid now f κ
           (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em)))
           (proj₂ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em))))
           sch sto)))))) →
  ∀ (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) → P ems sched st →
  depthBurst g bid now f κ ems sched st ≤ C
burst-le C g bid now f κ P hb hp []         sched st hs = z≤n
burst-le C g bid now f κ P hb hp (em ∷ ems) sched st hs =
  ⊔-lub (hb em ems sched st hs)
        (burst-le C g bid now f κ P hb hp ems _ _ (hp em ems sched st hs))

-- MOVING A CONSTANT SUMMAND ACROSS A TRADED SUM, which is what every
-- clause below needs once the ceiling's subject place carries a term
-- the step does not move: the trade is stated on the two places that
-- DO move, and the constant rides along.
shuffle : ∀ (a c s b s′ : ℕ) → a + s ≤ b + s′ → (a + c) + s ≤ (b + c) + s′
shuffle a c s b s′ h =
  ≤-trans (≤-reflexive (swap a c s))
          (≤-trans (+-monoˡ-≤ c h) (≤-reflexive (sym (swap b c s′))))
  where
  swap : ∀ (x y z : ℕ) → (x + y) + z ≡ (x + z) + y
  swap = solve 3 (λ x y z → (x :+ y) :+ z := (x :+ z) :+ y) refl

-- THE DRAIN, and it is ONE leaf for the three heads rather than three:
-- all of them delegate to `depthAll`, all of them wrap the subject in
-- exactly one nesting level, and none of them is distinguished by
-- anything the bound reads.  The payload subscribe under it is the one
-- descent that charges the path nothing, so this is where the size
-- factor is spent, and it is the head every program in the corpus wears
-- at its root.
--
-- AND THE HEAD'S OWN NODE IS FREE, which is what the `suc` in the
-- exponent is left over to pay for something else with.  A fresh
-- `*All` state carries no payload in any of its three spellings, so
-- the install moves the store not at all and the descent's ceiling can
-- be read back at the state the head was entered in.  Taking the state
-- as a free parameter would forfeit that: the store place would then
-- have to be paid for out of the head's own spare factor, and a queue
-- the caller pre-loaded is not bounded by anything the ceiling reads.
--
-- SO THE HEAD IS A BODY OVER TWO LEAVES AND THE FOLD ABOVE, and what
-- the split buys is that the fold is CHECKED rather than asserted: the
-- burst's invariant is `pushFitOK`, which is defined at a `∷` as its
-- head's fit times ITSELF at the tail and the stepped state, so the
-- fold's preservation premise is a projection and no leaf is owed for
-- it.  The grant the fit is taken at is the head's own spare factor --
-- the `suc` in the exponent that the descent half leaves unspent -- so
-- nothing here is calibrated freshly.
--
-- WHAT REMAINS IS AN ENTRY FIT AND A WALK, and they are the two halves
-- a state-only invariant could not separate.  A fold over the burst
-- cannot ask for its element bound at an ARBITRARY value list: the
-- frame that walks is handed the inners it subscribes, and nothing
-- outside the stream bounds those, so the invariant has to read the
-- stream and the entry has to establish it.  That is the leaf the
-- caller's hypotheses do not reach -- `inputsBelowᵉ` says nothing
-- about a store -- and it is where the caps facts the fit shelf
-- carries would have to arrive from.
--
-- PROBED: `Probed.Depth-Sighted` reads the PARENT at `root`, where this
--   head is the one it lands on -- the whole `⊔` rather than the burst
--   side alone, which dominates it -- at fold depths two and twenty:
--   descents of nine and eighty-one against ceilings of eleven and
--   thirty-four decimal digits.  On the family whose mergeAll is
--   unbounded, five against eleven digits; under the vocabulary that
--   connects at once rather than late, four against nineteen.  The
--   margin is the scale factor and it outruns every axis the corpus
--   moves.  Not covered: any `sl` past the two-slot vocabularies, which
--   is where both remaining families are; every path other than `root`,
--   which is the whole of what generalising added; the two heads
--   other than `mergeAllᵉ`, which no row reaches; and the burst side
--   read apart from the descent it is joined to.
postulate
  sight-all-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (k : ℕ) (op : AllOp) (nid : NodeId) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    (vals : List (Val Γ (obs u))) (fin : Bool)
    (sch : Sched Γ) (sto : EvalSt e) →
    T (inputsBelowᵉ k b) →
    thruFitOK (2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))
                 + k * slotWrapSum (Sched.slots sched))
      g op nid κ bid now vals sch sto →
    depthFrame g bid now (thru-outer op nid) κ vals fin sch sto
      ≤ sightCeil (sizeᵉ e) (2 ^ suc (syncSizeᵉ b) * (pathNestD κ + suc (nestDᵉ b))
                              + k * slotWrapSum (Sched.slots sched))
                  (storeNestMax sched st) (nestUnit e (Sched.slots sched))

-- THE GRANT READ AT ONE EMITTED VALUE, and then at a list and at a
-- stream.  These carry no STATE, which is the point of separating them
-- from the fit: what the outer frame needs of the payload's burst is a
-- property of the values and the telescope, so the threading the fit
-- does is discharged once here rather than being carried into the
-- payload's own descent.
--
-- AND THE SLOT SUMMAND IS THE VALUE'S, NOT THE FOLD'S.  An emitted
-- inner may be a slot REFERENCE, which carries neither depth nor size
-- to read, so the arrival-only reading is pinned at a constant -- at
-- the root it is pinned at ZERO -- while subscribing it runs the
-- slot's definition.  `inputsBelowᵉ` says which slots the value may
-- name and the wrap sum is what they hold, so the pair of them is the
-- charge, and it is read against the telescope the step is taken over
-- rather than against a schedule.
-- AND THERE IS NO TOWER HERE, WHICH IS THE WHOLE OF WHAT THIS FORMAT
-- ASKS.  A duplicating map doubles the ARRIVAL's size per layer while
-- costing the program a fixed number of constructors, so an exponent
-- read at the arrival is itself exponential in the program and nothing
-- read at the program bounds it.  What the arrival's size was standing
-- in for is its DEPTH, which moves by one a layer, and the delivery
-- agrees digit for digit: over four such layers the consume hands back
-- one, two, three, four.  Where a delivery HAS outrun the arrival's
-- depth it was a slot's definition doing it, and the summand beside
-- the depth is what pays for that.  So the charge is a sum of the two
-- things a consume can spend -- the telescope it is read under, and
-- what the slots the arrival may name hold -- with no factor at all.
-- REFUTED: `Refuted.Sight-All-Fit-Slot` pins the summand's half at the
--   reference, where the arrival-only grant is zero against a delivery
--   of sixty-four, and checks that the summand-carrying grant holds at
--   the deepest of those rows.
-- REFUTED: `Refuted.Sight-All-Stream-Dup.sight-all-stream-nest-absurd`
--   measures the exponents that ruled out the factor, two layers of
--   duplication up: sixteen, twenty-three, thirty, thirty-seven on the
--   program against eighteen, forty-two, ninety, a hundred and
--   eighty-six on the arrival.
ValFitP : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (sl : Slots Γ) (G P : ℕ)
  → Val Γ (obs u) → Set
ValFitP {u = u} k sl G P o =
  T (inputsBelowᵉ k o)
  × (P + nestDᵛ (obs u) o + k * slotWrapSum sl ≤ G)

ValsFitP : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (sl : Slots Γ) (G P : ℕ)
  → List (Val Γ (obs u)) → Set
ValsFitP k sl G P []       = ⊤
ValsFitP k sl G P (o ∷ os) = ValFitP k sl G P o × ValsFitP k sl G P os

StreamFitP : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (sl : Slots Γ) (G P : ℕ)
  → Stream Γ (obs u) → Set
StreamFitP k sl G P []                       = ⊤
StreamFitP {Γ = Γ} {u = u} k sl G P (em ∷ ems) =
  ValsFitP k sl G P (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em)))
  × StreamFitP k sl G P ems

-- AND THE PATH IS READ FOR ITS NESTING AND FOR NOTHING ELSE, so the
-- three above take that number and the three here are what a consumer
-- writes.  Splitting them is what lets the fold be stated at a path
-- and established at a LONGER one: the entry proves the charge under
-- the frame it pushed, and the head spends it under the path it was
-- entered at, which is the same statement at a smaller charge.
ValFit : ∀ {n} {Γ : Ctx n} {u t} (k : ℕ) (sl : Slots Γ) (G : ℕ)
  (κ : Path Γ u t) → Val Γ (obs u) → Set
ValFit k sl G κ = ValFitP k sl G (pathNestD κ)

ValsFit : ∀ {n} {Γ : Ctx n} {u t} (k : ℕ) (sl : Slots Γ) (G : ℕ)
  (κ : Path Γ u t) → List (Val Γ (obs u)) → Set
ValsFit k sl G κ = ValsFitP k sl G (pathNestD κ)

StreamFit : ∀ {n} {Γ : Ctx n} {u t} (k : ℕ) (sl : Slots Γ) (G : ℕ)
  (κ : Path Γ u t) → Stream Γ (obs u) → Set
StreamFit k sl G κ = StreamFitP k sl G (pathNestD κ)

-- BOTH PLACES MOVE THE SAME WAY, which is the whole content of the
-- split: a smaller charge and a larger grant are each a weakening, so
-- one lemma carries a fold from where it was proven to where it is
-- spent.
valsFitP-le : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (sl : Slots Γ) (G G′ P P′ : ℕ)
  (os : List (Val Γ (obs u))) → P ≤ P′ → G′ ≤ G →
  ValsFitP k sl G′ P′ os → ValsFitP k sl G P os
valsFitP-le k sl G G′ P P′ []       hp hg h        = tt
valsFitP-le {u = u} k sl G G′ P P′ (o ∷ os) hp hg (h , hs) =
  (proj₁ h
  , ≤-trans (+-monoˡ-≤ (k * slotWrapSum sl)
              (+-monoˡ-≤ (nestDᵛ (obs u) o) hp))
            (≤-trans (proj₂ h) hg))
  , valsFitP-le k sl G G′ P P′ os hp hg hs

streamFitP-le : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (sl : Slots Γ) (G G′ P P′ : ℕ)
  (str : Stream Γ (obs u)) → P ≤ P′ → G′ ≤ G →
  StreamFitP k sl G′ P′ str → StreamFitP k sl G P str
streamFitP-le k sl G G′ P P′ []         hp hg h        = tt
streamFitP-le k sl G G′ P P′ (em ∷ ems) hp hg (h , hs) =
  valsFitP-le k sl G G′ P P′ _ hp hg h
  , streamFitP-le k sl G G′ P P′ ems hp hg hs

-- WHAT ONE INNER COSTS TO SUBSCRIBE, and it is a claim about a VALUE
-- rather than about the payload's syntax -- which is why no reading of
-- the payload establishes it.  The outer frame does not FORWARD what
-- the payload emits: it subscribes it, so what has to be priced is the
-- emitted observable itself, and the currency has to be one that
-- survives the substitution the subscription performs.
-- REFUTED: `Refuted.Thru-Subscribe-Nest` kills the per-value form in
--   the additive currency -- an emitted value comes out deeper than
--   the observable it came from by the number of times the step
--   function names its payload, and that depth is a free parameter, so
--   no constant charge closes it.
-- PROBED: `Probed.Sight-Thru-Val` at the reference family the wrap was
--   added for.  The VALUE conjunct only: at a flat definition the wrap
--   vanishes and the grant is the path's own step, two against a
--   delivery of zero, which is the tight row; at the layered
--   definitions the grant outruns the delivery by orders that grow.  A
--   deferred tower is the shape that would hide depth under a zero
--   wrap and it delivers nothing at a consume, so that axis is
--   unavailable here rather than clear.  And the two STORE conjuncts
--   at the PARKING branch, which is the one that writes: over four
--   layers the store the park leaves goes one to four against a grant
--   of two to five, and the tight row parks onto a queue an earlier
--   consume wrote, where the reading MAXES and the conjunct holds at
--   equality off the incoming store alone.  The subscribing branch is
--   BLOCKED rather than untried: three families were driven through
--   it, including an inner `mergeAll` limited to one lane so the
--   subscription itself must park, and the store reads zero after
--   every one -- a minted node carries an empty queue.
postulate
  sight-thru-val : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (k : ℕ) (sl : Slots Γ) (G : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    ValFit k sl G κ o →
    let rc = thruConsume g op nid κ id now o sched st in
    (nestDᵛˢ (proj₁ rc) ≤ G)
    × (nodesMax (proj₂ (proj₂ (proj₂ rc))) ≤ nodesMax st ⊔ G)
    × ((j : NodeId) → nodeNestAt j (proj₂ (proj₂ (proj₂ rc))) ≤ nodeNestAt j st ⊔ G)

-- AND THE THREADING IS A FOLD OVER THAT, spending one value bound per
-- step: neither the grant nor the telescope moves, so the state the
-- previous consume left is only where the next one is read, never what
-- it is read against.
thruFit-vals : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : ℕ) (sl : Slots Γ) (G : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  ValsFit k sl G κ os → thruFitOK G g op nid κ id now os sched st
thruFit-vals k sl G g op nid κ id now []       sched st hsl _        = tt
thruFit-vals k sl G g op nid κ id now (o ∷ os) sched st hsl (h , hs) =
  proj₁ hv , proj₁ (proj₂ hv) , proj₂ (proj₂ hv)
  , thruFit-vals k sl G g op nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
      (trans (thruConsume-slots g op nid κ id now o sched st) hsl) hs
  where
  rc = thruConsume g op nid κ id now o sched st
  hv = sight-thru-val k sl G g op nid κ id now o sched st hsl h

pushFit-stream : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : ℕ) (sl : Slots Γ) (G : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  StreamFit k sl G κ str → pushFitOK G g op nid κ id now str sched st
pushFit-stream k sl G g op nid κ id now []         sched st hsl _        = tt
pushFit-stream {Γ = Γ} {u = u} k sl G g op nid κ id now (em ∷ ems) sched st
               hsl (h , hs) =
  thruFit-vals k sl G g op nid κ id now (proj₁ sp) sched st hsl h
  , pushFit-stream k sl G g op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
      (trans (stepFrame-slots g id now (thru-outer op nid) κ
                (proj₁ sp) (proj₂ (proj₂ sp)) sched st) hsl)
      hs
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame g id now (thru-outer op nid) κ
         (proj₁ sp) (proj₂ (proj₂ sp)) sched st

-- AND WHAT IS LEFT IS THE PAYLOAD'S OWN BURST, read as values.  It is
-- the half nothing here covers: a claim about the STORE the payload
-- subscribe hands back rather than about a descent, so no row that
-- computes a depth reaches it.
--
-- THE GRANT CARRIES THE SLOT SUMMAND, and it did not always.  A
-- payload may emit a slot REFERENCE, whose syntax says nothing about
-- what the slot holds, so a grant read off the payload alone is
-- pinned at a constant while subscribing the emitted inner runs the
-- slot's definition.  The summand every other bound on this face
-- carries is what pays for that, and adding it here costs the
-- consumer nothing: the walk leaf READS the fit, so a wider grant is
-- a weaker hypothesis there, and the ceiling both are spent under
-- already has the same summand.
--
-- AND THE PAYLOAD'S SIZE IS THE RIGHT EXPONENT ON THIS SIDE, WHICH IS
-- NOT A GENERAL LICENCE FOR IT.  A payload may MAP, and its step
-- function may name its argument twice; then one application emits a
-- term holding two copies of what arrived, so an emitted value's sync
-- size is about DOUBLE the payload's.  A tower is therefore owed, and
-- it is owed HERE, where the exponent is syntax of the program and
-- nothing between the two is substituted.  What may not carry one is
-- the charge the fold makes per ARRIVAL: an arrival is what the
-- substitution produced, so a tower over it has an exponent that is
-- itself exponential in the program and this grant cannot reach it.
--
-- REFUTED: `Refuted.Sight-All-Stream-Dup.sight-all-stream-dup-absurd`
--   kills the arrival-tower fold at a flat telescope where the wrap is
--   nought: sixteen against eighteen in the exponents, so a quarter of
--   a million demanded against this grant of a hundred and thirty-one
--   thousand.  And `…nest-absurd` again two layers up, where the same
--   rows measure the gap COMPOUNDING.
-- REFUTED: `Refuted.Sight-All-Fit-Slot` kills the payload-only grant
--   at a slot whose definition substitutes per layer -- delivered
--   `8 16 32 64` against a constant sixteen, meeting it exactly at the
--   third layer and doubling past it -- and pins the repair by
--   checking that the summand-carrying grant holds at the deepest of
--   those rows.  Not covered: the two heads other than `mergeAllᵒ`,
--   any path other than the one the row subscribes under, and the
--   store-growth conjuncts, which no row reads apart from the value one.
-- PROBED: `Probed.Sight-All-Stream` INHABITS the fold -- the statement
--   itself, not a boolean mirror of it -- at the duplicating payload
--   the refutations above are taken at, and at three layers of that
--   duplication.  The two columns are the receipt: the charge reads
--   one, two, three, four while the grant's exponent reads sixteen,
--   twenty-three, thirty, thirty-seven, so one side is linear in the
--   layer and the other a tower over something linear in it.  Not
--   covered: the two other heads; any path but `root`, which pins the
--   telescope summand at nought and the wrap with it; a telescope of
--   more than one slot; and an ARRIVAL that is a slot reference, which
--   is the one shape the wrap summand exists for.
postulate
  subscribeE-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (k : ℕ) (b : Closed Γ (obs u)) (κ : Path Γ (obs u) t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    T (inputsBelowᵉ k b) →
    StreamFitP k (Sched.slots sched)
      (2 ^ syncSizeᵉ b * (pathNestD κ + nestDᵉ b)
         + k * slotWrapSum (Sched.slots sched))
      (pathNestD κ)
      (proj₁ (subscribeE g b κ bid now sched st))

-- AND THE HEAD READS IT UNDER THE FRAME IT PUSHED, which is the whole
-- of what this clause is.  The leaf is stated at the path the payload
-- is actually subscribed under, so its charge counts the `thru-outer`
-- the head just built; the head spends it at the path it was entered
-- at, one shorter.  Both places move together -- the grant's sum is
-- the same number written with the `suc` on the other summand -- so
-- the step is a commutation and a weakening, and nothing about the
-- head's node, its limit or which of the three spellings it wears
-- reaches the leaf at all.
sight-all-stream : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (k : ℕ) (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  T (inputsBelowᵉ k b) →
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₀    = installNode nid (allFresh u op lim) st
      r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
  in StreamFit k (Sched.slots sched)
       (2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))
          + k * slotWrapSum (Sched.slots sched)) κ (proj₁ r)
sight-all-stream {u = u} g k op lim b κ bid now sched st ok =
  streamFitP-le k (Sched.slots sched)
    (2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b)) + k * W)
    (2 ^ syncSizeᵉ b * (suc (pathNestD κ) + nestDᵉ b) + k * W)
    (pathNestD κ) (suc (pathNestD κ)) (proj₁ r) (n≤1+n (pathNestD κ))
    (≤-reflexive (cong (λ z → 2 ^ syncSizeᵉ b * z + k * W)
                       (sym (+-suc (pathNestD κ) (nestDᵉ b)))))
    (subscribeE-fit g k b (thru-outer op nid ↠ κ) bid now sched₁ st₀ ok)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (allFresh u op lim) st
  r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
  W      = slotWrapSum (Sched.slots sched)

sight-all-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (k : ℕ) (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  T (inputsBelowᵉ k b) →
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₀    = installNode nid (allFresh u op lim) st
      r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
  in pushFitOK (2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))
                  + k * slotWrapSum (Sched.slots sched))
       g op nid κ bid now (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
sight-all-fit {u = u} g k op lim b κ bid now sched st ok =
  pushFit-stream k (Sched.slots sched)
    (2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))
       + k * slotWrapSum (Sched.slots sched))
    g op nid κ bid now (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
    (subscribeE-slots g b (thru-outer op nid ↠ κ) bid now sched₁ st₀)
    (sight-all-stream g k op lim b κ bid now sched st ok)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (allFresh u op lim) st
  r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀

sight-all-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (k : ℕ) (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  T (inputsBelowᵉ k b) →
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₀    = installNode nid (allFresh u op lim) st
      r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
  in depthBurst g bid now (thru-outer op nid) κ
       (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
     ≤ sightCeil (sizeᵉ e) (2 ^ suc (syncSizeᵉ b) * (pathNestD κ + suc (nestDᵉ b))
                             + k * slotWrapSum (Sched.slots sched))
                 (storeNestMax sched st) (nestUnit e (Sched.slots sched))
sight-all-drain {Γ = Γ} {e = e} {u = u} g k op lim b κ bid now sched st ok =
  burst-le C g bid now (thru-outer op nid) κ
    (pushFitOK G g op nid κ bid now)
    (λ em ems sch sto fit →
       sight-all-walk g k op nid b κ bid now sched st
         (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em)))
         (proj₂ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em))))
         sch sto ok (proj₁ fit))
    (λ em ems sch sto fit → proj₂ fit)
    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
    (sight-all-fit g k op lim b κ bid now sched st ok)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (allFresh u op lim) st
  r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
  G      = 2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))
             + k * slotWrapSum (Sched.slots sched)
  C      = sightCeil (sizeᵉ e)
             (2 ^ suc (syncSizeᵉ b) * (pathNestD κ + suc (nestDᵉ b))
               + k * slotWrapSum (Sched.slots sched))
             (storeNestMax sched st) (nestUnit e (Sched.slots sched))

-- ANY SUBSCRIBE'S DESCENT AGAINST WHAT IT CAN SEE, which is the
-- statement the induction is actually over.  A sweep crosses
-- `thru-outer` frames and drains bounded mergeAlls, and both are paid
-- for out of structure it already has: the subject it is descending,
-- the path it has built, the store it walks, and the program's own
-- wrap unit.  The entry claim is this at `root`, where the path
-- charges nothing and the two readings of the subject coincide.
--
-- THE SUBJECT AND THE PATH ARE ONE QUANTITY, and stating it that way
-- is the whole reason this form can be induced on.  Every structural
-- descent TRADES: a `map` moves its function's nesting off the subject
-- and onto the frame it pushes, a `*All` moves its own wrap `suc` the
-- same way, and a `scan` moves less than it drops.  So `pathNestD κ +
-- nestDᵉ b` is non-increasing along the walk while neither summand is,
-- and a bound stated on either alone has to be re-established at every
-- edge.
--
-- WHAT THE SIZE FACTOR PAYS FOR IS THE ONE DESCENT THAT DOES NOT
-- TRADE.  A drain runs under a `from-inner`, which the path measure
-- charges nothing for -- deliberately, since the layer it would charge
-- is the one the `thru-outer` above it already bought -- so a program
-- whose folds nest spends one per layer against a sum that sees none
-- of them.  The layers are bounded by the program, which is why the
-- size enters as a FACTOR rather than a summand: as a summand it is
-- outrun, one per delivered value against the descent's eight.
--
-- REFUTED: `Refuted.Nest-Depth-One` is the subscribe-side witness the
--   ceiling is calibrated against -- a limit-one mergeAll over three
--   queued inners under nested folds, read at the root subscribe, whose
--   descent climbs four per fold layer against the bare sum's three.
sight-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (k : ℕ) (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  T (inputsBelowᵉ k b) →
  depthAll g op (allFresh u op lim) b κ bid now sched st
    ≤ sightCeil (sizeᵉ e) (2 ^ suc (syncSizeᵉ b) * (pathNestD κ + suc (nestDᵉ b))
                            + k * slotWrapSum (Sched.slots sched))
                (storeNestMax sched st) (nestUnit e (Sched.slots sched))

depthE-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (k : ℕ) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → T (inputsBelowᵉ k b) →
  depthE g b κ bid now sched st ≤ Sight k b κ sched st
depthE-sighted g0 k (input i) κ bid now sched st ok
  with Sched.slots sched i
... | scripted _ = z≤n
... | shared d   = z≤n
depthE-sighted {e = e} (gs g) k (input i) κ bid now sched st ok
  with Sched.slots sched i in eqsl
... | scripted _        = z≤n
... | shared d {okd} =
  ≤-trans (depthE-sighted g (toℕ i) d (share-sink i) bid now sched st₁ okd)
          (sightCeil-sum (sizeᵉ e)
            (2 ^ syncSizeᵉ d * (0 + nestDᵉ d) + toℕ i * W)
            (storeNestMax sched st₁)
            (2 ^ 1 * (pathNestD κ + 0) + k * W)
            (storeNestMax sched st) (nestUnit e (Sched.slots sched)) step)
  where
  W  = slotWrapSum (Sched.slots sched)
  st₁ = register (toℕ i) κ
          (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
  wrap≤ : 2 ^ syncSizeᵉ d * (0 + nestDᵉ d) ≤ W
  wrap≤ = subst (λ w → slotWrap w ≤ W) eqsl (slotWrap≤sum (Sched.slots sched) i)
  strat : suc (toℕ i) * W ≤ k * W
  strat = *-monoˡ-≤ W (<ᵇ⇒< (toℕ i) k ok)
  store≤ : storeNestMax sched st₁ ≤ pathNestD κ + storeNestMax sched st
  store≤ = ≤-trans (storeNestMax-register (toℕ i) κ sched
                     (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                   (m⊔n≤m+n (pathNestD κ) (storeNestMax sched st))
  head≥ : pathNestD κ ≤ 2 ^ 1 * (pathNestD κ + 0)
  head≥ = ≤-trans (≤-reflexive (sym (+-identityʳ (pathNestD κ))))
                  (m≤m+n (pathNestD κ + 0) (pathNestD κ + 0 + 0))
  step : (2 ^ syncSizeᵉ d * (0 + nestDᵉ d) + toℕ i * W) + storeNestMax sched st₁
           ≤ (2 ^ 1 * (pathNestD κ + 0) + k * W) + storeNestMax sched st
  step =
    ≤-trans (+-mono-≤ (+-monoˡ-≤ (toℕ i * W) wrap≤) store≤)
    (≤-trans (+-monoˡ-≤ (pathNestD κ + storeNestMax sched st) strat)
    (≤-trans (≤-reflexive (sym (+-assoc (k * W) (pathNestD κ) (storeNestMax sched st))))
             (+-monoˡ-≤ (storeNestMax sched st)
               (≤-trans (+-monoʳ-≤ (k * W) head≥)
                        (≤-reflexive (+-comm (k * W) (2 ^ 1 * (pathNestD κ + 0))))))))
depthE-sighted g k (ofᵉ ts)           κ bid now sched st ok = z≤n
depthE-sighted g k emptyᵉ             κ bid now sched st ok = z≤n
depthE-sighted g k (deferᵉ b)         κ bid now sched st ok = z≤n
depthE-sighted g0 k (μᵉ body)         κ bid now sched st ok = z≤n
-- THE UNFOLD, which is the one descent whose subject is not a subterm
-- -- and it costs nothing, because both readings of the measure are
-- INVARIANT under the substitution: the copy a `μ` plants carries the
-- body's own nesting and the body's own sync size, and the head it
-- replaces charged a `suc` on top of each.
depthE-sighted {e = e} (gs g) k (μᵉ body) κ bid now sched st ok =
  ≤-trans (depthE-sighted g k (unfoldμ body) κ bid now sched st
             (ib-unfoldμ k body ok))
          (sightCeil-mono (sizeᵉ e) (nestUnit e (Sched.slots sched))
            (+-monoˡ-≤ (k * slotWrapSum (Sched.slots sched))
              (*-mono-≤ (^-monoʳ-≤ 2 (≤-trans (≤-reflexive (syncSize-unfoldμ body))
                                              (n≤1+n _)))
                        (+-monoʳ-≤ (pathNestD κ)
                                   (≤-reflexive (nestD-unfoldμ body)))))
            ≤-refl)
depthE-sighted g k (varᵉ ())        κ bid now sched st ok
-- THE SCAN, whose descent half IS the trade and whose store transport is
-- what the scale factor was minted for.  The trade is generous -- the
-- seed's and the function's nesting come off the subject and only the
-- function's goes onto the frame -- but the store takes the seed's back,
-- because the node a scan installs holds the EVALUATED seed and the
-- ceiling reads the store beside the measure.  So the two sides are
-- compared as one sum, and the spare the head's own `suc` buys is spent
-- on an evaluated seed's per-occurrence bound.
--
-- AND PER-OCCURRENCE IS THE ONLY BOUND AVAILABLE.  A closed term still
-- BINDS, and a branch may name what was bound on both sides of a sum
-- the observable measure takes, so an evaluated seed can outnest the
-- term that built it.
--
-- REFUTED: `Refuted.Eval-Seed-Nest` is the witness -- a `caseᵗ` whose
--   left branch names its bound observable both as a fold's SEED and
--   inside the source that fold runs over, weighing three against a
--   term that charges two, with the gap growing as the occurrence
--   count.  `Refuted.Apply-Fn-Nest` is the same failure with an
--   explicit payload rather than an empty environment.
depthE-sighted {e = e} g k (scanᵉ f z b) κ bid now sched st ok =
  ⊔-lub (≤-trans (depthE-sighted g k b (scan-f f nid ↠ κ) bid now sched₁ st₀
                    (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b)
                        (∧ʳ (inputsBelowᵗ k f)
                            (inputsBelowᵗ k z ∧ inputsBelowᵉ k b) ok)))
                 (sightCeil-sum (sizeᵉ e) (2 ^ syncSizeᵉ b * A + k * W)
                   (storeNestMax sched₁ st₀)
                   (2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b)) + k * W) sR
                   (nestUnit e (Sched.slots sched)) hsum′))
        (≤-trans (≤-reflexive (burst-flat g bid now (scan-f f nid) κ
                                 (λ _ _ _ _ → refl)
                                 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))) z≤n)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (scan-st (evalTm z)) st
  r      = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁ st₀
  K      = syncSizeᵉ (scanᵉ f z b)
  W      = slotWrapSum (Sched.slots sched)
  A      = nestDᵗ f + pathNestD κ + nestDᵉ b
  NV     = nodeNest (scan-st (evalTm z))
  sR     = storeNestMax sched st
  z≤K : syncSizeᵗ z ≤ K
  z≤K = ≤-trans (m≤n+m (syncSizeᵗ z) (syncSizeᵗ f))
                (≤-trans (m≤m+n _ (syncSizeᵉ b)) (n≤1+n _))
  b≤K : syncSizeᵉ b ≤ K
  b≤K = ≤-trans (m≤n+m (syncSizeᵉ b) _) (n≤1+n _)
  hNV : NV ≤ 2 ^ K * nestDᵗ z
  hNV = ≤-trans (evalTm-nest-sync z) (*-monoˡ-≤ (nestDᵗ z) (^-monoʳ-≤ 2 z≤K))
  eqv : 2 ^ K * A + 2 ^ K * nestDᵗ z ≡ 2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b))
  eqv = trans (sym (*-distribˡ-+ (2 ^ K) A (nestDᵗ z)))
              (cong (2 ^ K *_)
                (solve 4 (λ x y w v → (x :+ y :+ w) :+ v := y :+ (v :+ x :+ w))
                       refl (nestDᵗ f) (pathNestD κ) (nestDᵉ b) (nestDᵗ z)))
  hv : 2 ^ syncSizeᵉ b * A + NV
         ≤ 2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b))
  hv = ≤-trans (+-mono-≤ (*-monoˡ-≤ A (^-monoʳ-≤ 2 b≤K)) hNV)
               (≤-reflexive eqv)
  hsum : 2 ^ syncSizeᵉ b * (pathNestD (scan-f f nid ↠ κ) + nestDᵉ b)
           + storeNestMax sched₁ st₀
           ≤ 2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b)) + sR
  hsum =
    ≤-trans (+-monoʳ-≤ (2 ^ syncSizeᵉ b * A)
              (≤-trans (storeNestMax-install nid (scan-st (evalTm z)) sched₁ st)
                       (m⊔n≤m+n NV sR)))
            (≤-trans (≤-reflexive (sym (+-assoc (2 ^ syncSizeᵉ b * A) NV sR)))
                     (+-monoˡ-≤ sR hv))
  hsum′ : (2 ^ syncSizeᵉ b * (pathNestD (scan-f f nid ↠ κ) + nestDᵉ b) + k * W)
            + storeNestMax sched₁ st₀
            ≤ (2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b)) + k * W) + sR
  hsum′ = shuffle (2 ^ syncSizeᵉ b * (pathNestD (scan-f f nid ↠ κ) + nestDᵉ b))
                  (k * W) (storeNestMax sched₁ st₀)
                  (2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b))) sR hsum
depthE-sighted g k (mergeAllᵉ lim b) κ bid now sched st ok =
  sight-all g k mergeAllᵒ lim b κ bid now sched st ok
depthE-sighted g k (switchAllᵉ b)   κ bid now sched st ok =
  sight-all g k switchᵒ nothing b κ bid now sched st ok
depthE-sighted g k (exhaustAllᵉ b)  κ bid now sched st ok =
  sight-all g k exhaustᵒ nothing b κ bid now sched st ok
-- THE TAKE, whose descent half costs nothing on either side of the
-- trade: a take charges the path nothing and drops the subject nothing,
-- and the node it installs carries no nesting at all, so the reading the
-- recursive call gets is the reading this call was handed.  What is left
-- of the clause is its burst.
depthE-sighted {e = e} g k (takeᵉ c b) κ bid now sched st ok
  with evalTm c
... | zero  = z≤n
... | suc m =
  ⊔-lub (≤-trans (depthE-sighted g k b (take-f nid ↠ κ) bid now sched₁ st₀
                    (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok))
                 (sightCeil-mono (sizeᵉ e) (nestUnit e (Sched.slots sched))
                   (+-monoˡ-≤ (k * slotWrapSum (Sched.slots sched))
                     (*-monoˡ-≤ (pathNestD κ + nestDᵉ b)
                       (^-monoʳ-≤ 2 (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ c))
                                             (n≤1+n _)))))
                   (≤-trans (storeNestMax-install nid (take-st (suc m)) sched₁ st)
                            (⊔-lub z≤n ≤-refl))))
        (≤-trans (≤-reflexive (burst-flat g bid now (take-f nid) κ
                                 (λ _ _ _ _ → refl)
                                 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))) z≤n)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc m)) st
  r      = subscribeE g b (take-f nid ↠ κ) bid now sched₁ st₀

-- THE ONE CLAUSE THAT IS THE TRADE ITSELF, and it needs no store
-- transport: a map mints nothing, so the state the recursive call reads
-- is the state this call was handed.  The whole step is the charge
-- moving off the subject and onto the frame, which is an associativity
-- and a commutativity on the measure and nothing else.
depthE-sighted {e = e} g k (mapᵉ f b) κ bid now sched st ok =
  ⊔-lub (≤-trans (depthE-sighted g k b (map-f f ↠ κ) bid now sched st
                    (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok))
                 (sightCeil-mono (sizeᵉ e) (nestUnit e (Sched.slots sched))
                   (+-monoˡ-≤ (k * slotWrapSum (Sched.slots sched))
                     (*-mono-≤ (^-monoʳ-≤ 2 (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f))
                                                     (n≤1+n _)))
                               (≤-reflexive (trade f b κ))))
                   ≤-refl))
        (≤-trans (≤-reflexive (burst-flat g bid now (map-f f) κ
                                 (λ _ _ _ _ → refl)
                                 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))) z≤n)
  where
  r = subscribeE g b (map-f f ↠ κ) bid now sched st
  trade : ∀ {s u} (f : Fn _ [] [] [] s u) (b : Closed _ s) (κ : Path _ u _) →
    pathNestD (map-f f ↠ κ) + nestDᵉ b ≡ pathNestD κ + nestDᵉ (mapᵉ f b)
  trade f b κ = trans (cong (_+ nestDᵉ b) (+-comm (nestDᵗ f) (pathNestD κ)))
                      (+-assoc (pathNestD κ) (nestDᵗ f) (nestDᵉ b))

-- THE HEAD ITSELF, and it is a real body now rather than a claim: the
-- descent half is the same trade every structural clause makes -- the
-- wrap's own nesting level comes off the subject and onto the path the
-- payload is subscribed under, so the two readings differ by a `suc`
-- that commutes across the sum -- and the head's `suc` in the exponent
-- is left entirely unspent by it.  What the assembly does NOT close is
-- the burst: a `thru-outer` frame is the one frame that walks, and the
-- walk is where the drain lives.
sight-all {e = e} {u = u} g k op lim b κ bid now sched st ok = ⊔-lub sub drn
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (allFresh u op lim) st
  W      = slotWrapSum (Sched.slots sched)
  S      = syncSizeᵉ b
  A      = pathNestD κ + suc (nestDᵉ b)
  sR     = storeNestMax sched st

  store≤ : storeNestMax sched₁ st₀ ≤ sR
  store≤ = ≤-trans (storeNestMax-install nid (allFresh u op lim) sched₁ st)
                   (≤-reflexive (cong (_⊔ sR) (allFresh-nest u op lim)))

  coef : 2 ^ S * (suc (pathNestD κ) + nestDᵉ b) ≤ 2 ^ suc S * A
  coef = ≤-trans (≤-reflexive (cong (2 ^ S *_) (sym (+-suc (pathNestD κ) (nestDᵉ b)))))
                 (*-monoˡ-≤ A (^-monoʳ-≤ 2 (n≤1+n S)))

  hsum : (2 ^ S * (suc (pathNestD κ) + nestDᵉ b) + k * W) + storeNestMax sched₁ st₀
           ≤ (2 ^ suc S * A + k * W) + sR
  hsum = +-mono-≤ (+-monoˡ-≤ (k * W) coef) store≤

  sub : depthE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
          ≤ sightCeil (sizeᵉ e) (2 ^ suc S * A + k * W) sR
              (nestUnit e (Sched.slots sched))
  sub = ≤-trans (depthE-sighted g k b (thru-outer op nid ↠ κ) bid now sched₁ st₀ ok)
                (sightCeil-sum (sizeᵉ e)
                   (2 ^ S * (suc (pathNestD κ) + nestDᵉ b) + k * W)
                   (storeNestMax sched₁ st₀)
                   (2 ^ suc S * A + k * W) sR
                   (nestUnit e (Sched.slots sched)) hsum)

  drn = sight-all-drain g k op lim b κ bid now sched st ok
