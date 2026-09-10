-- ══════════════════════════════════════════════════════════════════
-- THE WALK'S BURST LEDGER CANNOT BE READ AT THE ENTRY INSTANT'S SIZE
-- CAP.  The count a walk carries GROWS along the path, the caps side
-- grows with it level by level, and the burst side is stated at ONE
-- fixed number -- so a lemma taking the walk's caps package and
-- returning the burst package at the flat entry size is false.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHY THE GENERIC FORM IS THE ONE THAT MATTERS.  The ledger's own
-- statement fixes the cap at the entry instant's recurrence value,
-- whose fields are iterates the tower seals, so no row can compute
-- them and no witness can contradict that statement directly.  What a
-- PROOF can read is exactly what survives the seal: the caps package
-- as a predicate over an arbitrary triple.  So the caps-generic lemma
-- is not a weakening chosen for convenience -- it is the strongest
-- statement any route through the walk may use, and refuting it says
-- the route is closed however large the sealed numerals turn out.
--
-- WHERE THE TWO SIDES PART.  The caps package carries a LEVEL and
-- re-reads its cap at `frameStep Lv c` at every frame, so the number
-- it charges against climbs as the walk descends; the burst package
-- charges every clause against ONE `W`.  A crossing frame emits each
-- arrival's whole burst, so the count climbs too -- and the level is
-- exactly what the caps side spends to pay for that.  Fixing `W` at
-- the entry size gives the burst side none of it.
--
-- THE WITNESS RUNS AT LEVEL ZERO, which is what makes it a statement
-- about the SIDE and not about the level arithmetic: every step is
-- taken with no level spent at all, so the caps package holds at the
-- flat cap and the burst package is refuted at that same flat cap.
-- Nothing here needs the sealed step count, since a zero increment
-- discharges its bound at `z≤n`.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Burst-Entry-Size where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; length)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Maybe using (nothing)

open import Rx.Prim using (Gas; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; _↠_; thru-outer; mergeAllᵒ;
         mergeAll-st; installNode; st-init; stepFrame)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Nest-Walk using (capsWalkOK; burstsOK)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Walk-Burst-Additive
  using (slots; gas; sched; vals; e₀)

-- THE CHAIN IS BUILT IN SUBSCRIPTION ORDER, which the caps package now
-- reads as a conjunct: a head is minted after everything under it, so
-- the outer frame carries the LARGER node id and the whole chain names
-- only cells the scheduler's counter has already handed out.  Nothing
-- about the burst arithmetic below turns on it -- the ordering is a
-- reading of the node table and the counter, and the counts are a
-- reading of what a crossing frame emits.
outer : Frame Γ₂ (obs (obs (obs natᵗ))) (obs (obs natᵗ))
outer = thru-outer mergeAllᵒ 1

inner : Frame Γ₂ (obs (obs natᵗ)) (obs natᵗ)
inner = thru-outer mergeAllᵒ 0

-- the whole walk, taken from the top rather than one frame at a time
path₀ : Path Γ₂ (obs (obs (obs natᵗ))) (obs natᵗ)
path₀ = outer ↠ (inner ↠ root)

stᵒ : EvalSt e₀
stᵒ = installNode 0 (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
        (installNode 1 (mergeAll-st {t = obs (obs natᵗ)} nothing 0 [] false)
          (st-init e₀))

-- the counter stands above every cell the chain names, which is what a
-- run that minted the chain leaves behind
schedᵒ : Sched Γ₂
schedᵒ = record (sched 6) { nextNode = 2 }

cap : Caps
cap = caps 35 4000 4000

walkOK :
  capsWalkOK cap cap (slots 6) 0 0 gas 0 0 0 path₀ vals false schedᵒ stᵒ
walkOK =
  refl , refl , ≤ᵇ⇒≤ _ _ tt , refl , refl , tt ,
  refl , refl ,
  refl , refl ,
  0 , z≤n ,
  (refl , refl , ≤ᵇ⇒≤ _ _ tt , refl , refl , tt ,
   refl , refl ,
   refl , refl ,
   0 , z≤n , refl)

-- the two crossings, taken exactly as the walk's own recursion takes
-- them, so the pinned counts are the ones the refuted conjunct is read
-- against rather than a neighbouring run's
stepA : _
stepA = stepFrame gas 0 0 outer (inner ↠ root) vals false schedᵒ stᵒ

stepB : _
stepB = stepFrame gas 0 0 inner root (proj₁ stepA)
          (proj₁ (proj₂ (proj₂ stepA)))
          (proj₁ (proj₂ (proj₂ (proj₂ stepA))))
          (proj₂ (proj₂ (proj₂ (proj₂ stepA))))

handed≡6 : length (proj₁ stepA) ≡ 6
handed≡6 = refl

delivered≡36 : length (proj₁ stepB) ≡ 36
delivered≡36 = refl

size≡35 : Caps.cSize cap ≡ 35
size≡35 = refl

walk-burst-entry-size-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (c ac : Caps) (sl : Slots Γ) (d Lv : ℕ) (sf : Gas) (g : ℕ) (i : Id) (now : Tick)
     (p : Path Γ u t) (v : List (Val Γ u)) (fin : Bool) (sc : Sched Γ) (st : EvalSt e) →
     2 ≤ Caps.cSize c →
     Sched.slots sc ≡ sl →
     capsWalkOK c ac sl d Lv sf g i now p v fin sc st →
     burstsOK (Caps.cSize c) sf g i now p v fin sc st) → ⊥
walk-burst-entry-size-absurd h =
  ≤⇒≤ᵇ (proj₂ (proj₂ (proj₂ (proj₂
    (h cap cap (slots 6) 0 0 gas 0 0 0 path₀ vals false schedᵒ stᵒ
       (s≤s (s≤s z≤n)) refl walkOK)))))
