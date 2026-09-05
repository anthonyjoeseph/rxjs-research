-- ══════════════════════════════════════════════════════════════════
-- THE INNER FRAME'S POTENTIAL ARMS CHARGE THE NODE TABLE AND NO PREMISE
-- OF EITHER BOUNDS IT, so both are FALSE as written -- unbounded, at
-- states the statements themselves quantify over.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENTS SAID.  A `from-inner` frame surrenders the path's
-- factor and asks that what it hands on fits the instant's potential:
-- the factor times the frame's own grant, whose multiplicand is the
-- node's nesting JOINED with the values' and one unit beside it.  The
-- quiet arm takes the grant at width zero because a drain that finds no
-- cell subscribes nothing; the drain arm takes it at the queue's own
-- width.  Their premises are about the schedule, the path, the values
-- in flight, and -- in the drain arm alone -- which constructor the
-- cell holds.
--
-- WHY IT LOOKED RIGHT.  The join reads as a widening of the values' own
-- depth, which the potential premise does bound -- and at every state a
-- run actually reaches, the node the frame names was installed by a
-- subscribe the same cascade performed, so the table's depth and the
-- values' move together.  That is a fact about reachable states and the
-- statement is not about those.
-- ══════════════════════════════════════════════════════════════════

-- WHERE IT BREAKS.  `nodeNestAt` reads one accumulator out of the node
-- table, and no hypothesis here constrains the table at all: the level
-- is met at zero, the values are empty, the path below the frame is the
-- root, and the potential premise is an `all` over an empty list.  So
-- the left side is at least the accumulator's own depth while the right
-- side is fixed by the program, the slots and the instant -- and one
-- `scanᵉ` cell holding a payload `k` layers deep sends `k` through.  The
-- row below is parametric in `k` for that reason: the potential is
-- SEALED and computes nowhere, so the witness is taken one above it
-- rather than at a numeral.

-- WHAT DIES AND WHAT DOES NOT.  Both inner arms die, and the second row
-- below is the drain arm rather than an argument that it follows: its
-- extra premise pins the cell's SHAPE and says nothing about its depth,
-- so the queue it names carries the payload instead of the accumulator
-- and the same reading runs away.  The walk's through arm is untouched:
-- it builds its grant out of the path's depth, the depth in flight and
-- the context's wrap, and reads the table nowhere.  What the two inner
-- arms owe is the ambient store predicate the cascade doors already
-- carry; whether the grant is AFFORDABLE once it has that is a separate
-- question this says nothing about, since the factor is read at the
-- walk's level and both witnesses are taken at the entry.

-- WHAT IS HAND-BUILT, AND WHY IT DOES NOT SOFTEN THE FINDING.  The
-- state is `st-init` plus ONE `installNode`, and the statement
-- quantifies over every `st` with no reachability side condition, so
-- this refutes it as written -- the same freedom `Refuted.Chain-Step-
-- Nodes` spends on the path.  Nor is the cell an unreachable shape: a
-- `scanᵉ` whose seed is an observable installs exactly it, and the
-- payload is the one `Refuted.Chain-Step-Live-Nest` already reaches
-- through a delivery.
module Refuted.Inner-Phi-Store where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; _+_; _*_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; ≤⇒≤ᵇ; m≤m⊔n; m≤m+n; *-identityˡ;
         *-monoˡ-≤; ⊔-identityʳ; 1+n≰n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Decide using (T⇒≡true)
open import Rx.Prim using (Gas; g0; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeId; Path; root; _↠_; from-inner; AllOp; mergeAllᵒ;
         scan-st; mergeAll-st; lookupNode; installNode; st-init; sched-init)
open import Verify-Budget-Sufficient.Caps
  using (Caps; capsAt; capsH; frameStep; sizeCount; 2≤capsAt-size)
open import Verify-Budget-Sufficient.Caps-Depth using (depthReact)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU; 1≤nestFac)
open import Verify-Budget-Sufficient.Nest-Store
  using (pathNestD; nestUnit; nestCapAt)
open import Verify-Budget-Sufficient.Nest-Walk using (nodeNestAt; nestDᵛˢ)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestΦAt)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Chain-Step-Live-Nest using (deepV; prog; slots)

----------------------------------------------------------------------
-- THE FIRST STATEMENT, restated verbatim so that a reader diffs two
-- texts rather than trusting a summary of one.
----------------------------------------------------------------------
InnerΦQuiet : Set
InnerΦQuiet = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  ∀ (j : ℕ) →
    j ≤ sizeCount (capsAt e sl id)
                  (depthReact sf op allNid inst p eid now vals sched st fin)
        ⊔ Caps.cSize (capsAt e sl id) →
    pathΦF (Caps.cSize (capsAt e sl id)) p
      * (nestFac (Caps.cSize (frameStep j (capsAt e sl id))) 0
           * ((nodeNestAt allNid st ⊔ nestDᵛˢ vals)
              + nestU (Caps.cSize (frameStep j (capsAt e sl id)))
                      (nestUnit e (Sched.slots sched)))
         + pathΦD (Caps.cSize (capsAt e sl id)) p)
    ≤ nestΦAt e sl id

----------------------------------------------------------------------
-- THE STATE THE STATEMENT ADMITS, and the depth it carries.  One cell,
-- installed at the id the frame names, holding a payload `k` layers
-- deep -- so the reading the arm charges is `k` and nothing else about
-- the instant changes with it.
----------------------------------------------------------------------
stOf : ℕ → EvalSt prog
stOf k = installNode 0 (scan-st {t = obs natᵗ} (deepV k)) (st-init prog)

deepNest : ∀ (k : ℕ) → nestDᵛ (obs natᵗ) (deepV k) ≡ k
deepNest zero    = refl
deepNest (suc k) = cong suc (trans (⊔-identityʳ _) (deepNest k))

nodeNest≡ : ∀ (k : ℕ) → nodeNestAt 0 (stOf k) ≡ k
nodeNest≡ = deepNest

----------------------------------------------------------------------
-- THE PREMISES AT THE WITNESS, and every one of them is met the cheap
-- way, which is the point: the arm is asked for its conclusion exactly
-- where it is asked for the least.
----------------------------------------------------------------------
S : ℕ
S = Caps.cSize (capsAt prog slots 0)

1≤S : 1 ≤ S
1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size prog slots 0)

pth : Path Γ₂ natᵗ natᵗ
pth = from-inner mergeAllᵒ 0 0 ↠ root

legal : pathSz? S pth ≡ true
legal = cong (_∧ true) (T⇒≡true (1 ≤ᵇ S) (≤⇒≤ᵇ 1≤S))

-- LOAD-BEARING: it is the conjunct a reader expects to carry the
-- table, and at an empty burst it carries nothing at all.
premΦ : valsΦ? S (nestΦAt prog slots 0) pth [] ≡ true
premΦ = refl

----------------------------------------------------------------------
-- THE ARITHMETIC THE CONCLUSION SURRENDERS, stated over the shape and
-- not over the arm's own quantities, so that a restatement of the
-- factor or of the unit leaves it untouched: a positive factor and a
-- positive path weight can only inflate what they multiply.
----------------------------------------------------------------------
lift : ∀ (Q F X U D k : ℕ) → 1 ≤ Q → 1 ≤ F → k ≤ X →
  k ≤ Q * (F * (X + U) + D)
lift Q F X U D k 1≤Q 1≤F k≤X =
  ≤-trans k≤X
    (≤-trans (m≤m+n X U)
      (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (X + U))))
                        (*-monoˡ-≤ (X + U) 1≤F))
        (≤-trans (m≤m+n (F * (X + U)) D)
          (≤-trans (≤-reflexive (sym (*-identityˡ (F * (X + U) + D))))
                   (*-monoˡ-≤ (F * (X + U) + D) 1≤Q)))))

----------------------------------------------------------------------
-- THE ROW.  Every `k` is under the instant's potential, so the
-- potential is above its own successor -- which no natural is.
----------------------------------------------------------------------
inner-phi-store-absurd : InnerΦQuiet → ⊥
inner-phi-store-absurd h = 1+n≰n (bound (suc (nestΦAt prog slots 0)))
  where
  bound : ∀ (k : ℕ) → k ≤ nestΦAt prog slots 0
  bound k =
    ≤-trans
      (lift _ _ _ _ _ k ≤-refl (1≤nestFac _ 0)
        (≤-trans (≤-reflexive (sym (nodeNest≡ k))) (m≤m⊔n _ _)))
      (h slots 0 g0 0 0 mergeAllᵒ 0 0 root [] false (sched-init prog slots)
         (stOf k) refl legal z≤n premΦ 0 z≤n)

----------------------------------------------------------------------
-- THE SECOND STATEMENT, the same arm with a queue: the grant's width is
-- the drain's own and the level range is the round's count rather than
-- the reaction's.  Neither is what fails.
----------------------------------------------------------------------
InnerΦDrain : Set
InnerΦDrain = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
  lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  ∀ (j : ℕ) →
    j ≤ sizeCount (capsAt e sl id) (capsH e sl id)
        ⊔ Caps.cSize (capsAt e sl id) →
    pathΦF (Caps.cSize (capsAt e sl id)) p
      * (nestFac (Caps.cSize (frameStep j (capsAt e sl id)))
                 (drainW sf allNid p eid now q sched st)
           * ((nodeNestAt allNid st ⊔ nestDᵛˢ vals)
              + nestU (Caps.cSize (frameStep j (capsAt e sl id)))
                      (nestUnit e (Sched.slots sched)))
         + pathΦD (Caps.cSize (capsAt e sl id)) p)
    ≤ nestΦAt e sl id

----------------------------------------------------------------------
-- THE STATE THAT ARM ADMITS.  The cell IS a merge at the frame's own
-- type, so the premise the quiet arm does not have is met on the nose --
-- and the queue it parks is what the reading runs away on.
----------------------------------------------------------------------
stQ : ℕ → EvalSt prog
stQ k =
  installNode 0 (mergeAll-st {t = natᵗ} nothing 0 (deepV k ∷ []) false)
              (st-init prog)

-- LOAD-BEARING: it is the premise a reader expects to carry the cell's
-- content, and it carries the cell's CONSTRUCTOR.
parked : ∀ (k : ℕ) →
  lookupNode 0 (EvalSt.nodes (stQ k))
    ≡ just (mergeAll-st {t = natᵗ} nothing 0 (deepV k ∷ []) false)
parked k = refl

nodeNestQ≡ : ∀ (k : ℕ) → nodeNestAt 0 (stQ k) ≡ k
nodeNestQ≡ k = trans (⊔-identityʳ _) (deepNest k)

inner-phi-drain-store-absurd : InnerΦDrain → ⊥
inner-phi-drain-store-absurd h = 1+n≰n (bound (suc (nestΦAt prog slots 0)))
  where
  bound : ∀ (k : ℕ) → k ≤ nestΦAt prog slots 0
  bound k =
    ≤-trans
      (lift _ _ _ _ _ k ≤-refl (1≤nestFac _ _)
        (≤-trans (≤-reflexive (sym (nodeNestQ≡ k))) (m≤m⊔n _ _)))
      (h slots 0 g0 0 0 mergeAllᵒ 0 0 root [] false (sched-init prog slots)
         (stQ k) nothing 0 (deepV k ∷ []) false
         (parked k) refl legal z≤n premΦ 0 z≤n)
