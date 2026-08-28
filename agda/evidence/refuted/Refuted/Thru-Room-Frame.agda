-- ══════════════════════════════════════════════════════════════════
-- THE FRAME CANNOT DERIVE THE ROOM RECORD FROM ITS CAPS, and the
-- reason is that the caps and the record read the same width field
-- against two different quantities.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A frame at a `*All` head, handed the caps
-- invariant at the state it starts from and values that invariant's own
-- predicate admits, can hand the walk below it the room record every
-- consume spends -- so that the record is owed once, at the frame,
-- rather than once per arrival.
--
-- WHERE IT BREAKS.  The record's queue conjunct bounds `suc (length q)`
-- by the width field, where `q` is what the node already holds; the
-- caps invariant bounds the queue's own length by that same field.  A
-- node holding exactly as many entries as the field allows therefore
-- satisfies the caps and refutes the record, and it does so at the
-- FIRST arrival -- no walk is needed, and the length premise is not
-- what is doing the work.
--
-- THE WITNESS is the parking state its sibling refutation already
-- uses: a merge whose limit is spent, one entry queued, and the caps
-- read tightly off the arrival, which puts the width field at one.
-- Every other premise of the frame statement is pinned true where the
-- row runs, the width half of the record included -- that half is
-- discharged here at the frame's own measure rather than assumed, so
-- the contradiction is the caps half alone.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about whether the record
-- is derivable at a STEPPED cap, which is where the caps face's own
-- preservation for this machinery lands and where the repair points;
-- and it says nothing about the frame's fit, which no longer depends
-- on the caps half being derivable at all.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Room-Frame where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ;
         varᵗ; caseᵗ; inlᵗ; syncSizeᵛ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path; _↠_; thru-outer;
         mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Burst using (innerW)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestClosOK?; thruRoomOK)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

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

-- the limit is SPENT, so the node holds exactly what its width allows
st₀ : EvalSt prog
st₀ = installNode 7 (mergeAll-st {t = obs natᵗ} (just 1) 1 (arr 3 ∷ []) false)
                 (st-init prog)

cap : Caps
cap = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 6))
           (pWᵛ 2 slots (obs (obs natᵗ)) (arr 6)) 0

vals : List (Val Γ₂ (obs (obs natᵗ)))
vals = arr 6 ∷ []

-- the frame's own burst measure, taken as the width rather than
-- guessed, so the record's width half is discharged and not assumed
W : ℕ
W = suc (innerW gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ st₀)

-- the premises, pinned true where the row runs rather than assumed
prems : Bool × Bool × Bool
prems = capsOK? cap sched₀ st₀
      , all (valCaps? cap slots (obs (obs natᵗ))) vals
      , all (nestClosOK? cap slots) vals

prems≡ : prems ≡ (true , true , true)
prems≡ = refl

slots≡ : Sched.slots sched₀ ≡ slots
slots≡ = refl

size≤ : slotsSize slots ≤ Caps.cSize cap
size≤ = ≤ᵇ⇒≤ (slotsSize slots) (Caps.cSize cap) tt

1≤W : 1 ≤ W
1≤W = s≤s z≤n

len≤W : length vals ≤ W
len≤W = s≤s z≤n

-- THE STATEMENT, spelled out here rather than named, because the
-- repair it forces changes the premises: what is refuted is that the
-- CAPS supply the room record, and a later form may supply the queue
-- bound from the burst record instead.
Stmt : Set
Stmt =
  Sched.slots sched₀ ≡ slots →
  1 ≤ W → length vals ≤ W →
  capsOK? cap sched₀ st₀ ≡ true →
  all (valCaps? cap slots (obs (obs natᵗ))) vals ≡ true →
  slotsSize slots ≤ Caps.cSize cap →
  all (nestClosOK? cap slots) vals ≡ true →
  thruRoomOK cap W gasBig mergeAllᵒ 7 κ 0 0 vals sched₀ st₀

room-absurd : Stmt → ⊥
room-absurd h
  with h slots≡ 1≤W len≤W refl refl size≤ refl
... | (_ , queue , _ , _) , _ with queue (just 1) 1 (arr 3 ∷ []) false refl
...   | s≤s ()

-- WHICH FIELD, since the repair differs: the caps admit a queue of one
-- against a width of one, and the record asks the same field for two
figs : ℕ × ℕ
figs = Caps.cWid cap , length (arr 3 ∷ [])

figs≡ : figs ≡ (1 , 1)
figs≡ = refl
