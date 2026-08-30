-- ══════════════════════════════════════════════════════════════════
-- THE CONSUME STEP CANNOT PROMISE THE CAPS INVARIANT IT IS HANDED, and
-- the reason has no arithmetic in it: the premise on the arriving value
-- bounds its SIZE and says nothing about its WIDTH, while the invariant
-- the step must hand on bounds both.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A step at a `*All` head, run under the nest
-- face's caps invariant and handed a value that invariant's own value
-- predicate admits, leaves a state the same invariant still holds at --
-- which is what lets the walk re-enter at the state the previous
-- arrival left.
--
-- WHERE IT BREAKS, and it is not where it looks.  The invariant's node
-- conjunct bounds a merge node's queue TWO ways against the one width
-- field: every queued value's frame width, and the queue's LENGTH.  The
-- arrival here is admitted on size, and its width is inside the field
-- exactly -- both read 1.  What flips is the length: the no-room arm
-- appends the arrival, the queue goes from one entry to two, and two is
-- not inside a field of one.
--
-- SO A WIDTH PREMISE ON THE ARRIVING VALUE CANNOT REPAIR IT.  No fact
-- about the value reaches a bound on how many of them the node already
-- holds; what the step is missing is room at the NODE, which none of
-- its hypotheses mentions.  That is the conclusion-needs-what-no-
-- hypothesis-carries shape, and it is why this is a restatement rather
-- than a grind.
--
-- THE WITNESS is a merge whose limit is already spent, so the parking
-- arm is the one taken, with the caps read tightly off the arrival --
-- the same reading every probe in this campaign uses.  The other four
-- conjuncts of the invariant survive, the size half included.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about the grant, which is
-- the risk the step's other three conjuncts carry, and it does not make
-- the caps conjunct unprovable -- it says the arrival needs a WIDTH
-- premise beside its size one, matching the conjunct that reads it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Step-Caps where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ;
         varᵗ; caseᵗ; inlᵗ; syncSizeᵛ)
open import Rx.Frame-Width using (pWᵛ; pWᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path; _↠_; thru-outer;
         mergeAllᵒ; installNode; mergeAll-st; thruConsume)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestCapsOK?)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

E : ℕ → Val Γ₂ (obs natᵗ)
E zero    = ofᵉ (nat̂ 0 ∷ [])
E (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (E k) ∷ []))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

arr : ℕ → Val Γ₂ (obs (obs natᵗ))
arr k = mapᵉ dup (ofᵉ (strmᵗ (E k) ∷ []))

κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

sched₀ : Sched Γ₂
sched₀ = sched-init prog slots

-- the limit is SPENT, so the arm that parks is the one taken
st₀ : EvalSt prog
st₀ = installNode 7 (mergeAll-st {t = obs natᵗ} (just 1) 1 (arr 3 ∷ []) false)
                 (st-init prog)

cap : Caps
cap = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 6))
           (pWᵛ 2 slots (obs (obs natᵗ)) (arr 6)) 0

-- the premises, pinned true where the row runs rather than assumed:
-- the slots the walk re-enters at, the invariant going in, and the
-- value predicate that admits the arrival
prems : Bool × Bool
prems = nestValOK? cap (obs (obs natᵗ)) (arr 6)
      , nestCapsOK? cap sched₀ st₀

capsPrems≡ : prems ≡ (true , true)
capsPrems≡ = refl

slots≡ : Sched.slots sched₀ ≡ slots
slots≡ = refl

r : _
r = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ st₀

-- and the invariant coming out, which is the conjunct the step claims
after : Bool
after = nestCapsOK? cap (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

after≡false : after ≡ false
after≡false = refl

thru-step-caps-absurd : after ≡ true → ⊥
thru-step-caps-absurd ()

-- WHICH HALF, since the repair differs: the node predicate bounds the
-- queue's values AND its LENGTH against the same width field, and a
-- premise about the arriving value cannot reach the second one
widths : ℕ × ℕ
widths = Caps.cWid cap , pWᵉ 2 slots (arr 6)

widths≡ : widths ≡ (1 , 1)
widths≡ = refl
