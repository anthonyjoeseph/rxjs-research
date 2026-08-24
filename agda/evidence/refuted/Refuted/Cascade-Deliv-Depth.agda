-- ══════════════════════════════════════════════════════════════════
-- A CASCADE'S DESCENT IS NOT PAID FOR PER DELIVERY, and the mechanism
-- is the drain, exactly as it is on the subscribe side.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  One arrival's whole cascade descends no
-- deeper than its payload, the nesting of the chains it walks, the
-- store it starts from, and ONE `nestSyn` per DELIVERY on the
-- evaluator's own ledger — the tight half of the width-denominated
-- bound its consumer spends, split out so that the counting question
-- could be settled statically.
--
-- WHY IT LOOKED RIGHT.  `nestSyn` is a SYNTACTIC ceiling on nesting, so
-- deepening what a delivery stores deepens the ceiling by the same
-- step, and a charge in that currency cannot be outrun by depth.
--
-- WHERE IT BREAKS, AND IT IS NOT THE PHANTOM BRANCH.  A BOUNDED
-- mergeAll parks its overflow, and the DRAIN that releases it runs as a
-- walk under a finishing frame — a `from-inner`, which `pathNestD`
-- charges nothing for.  So the drain's levels have no path term to come
-- out of and must come out of the per-delivery charge, and a program
-- whose folds nest spends arbitrarily many of them on ONE delivery.
-- The witness below reads ONE chain, ONE delivery and NO cancellation:
-- the skip branch that the statement's recorded dead route is about is
-- not entered at all, and the live arm alone is enough.
--
-- THE WITNESS is `progU 3 2` — a limit-1 mergeAll over three inners, so
-- the drain fires — at the two-slot vocabulary `insF 1 2 2`, whose
-- second slot is HOT, which is what makes the program produce cascades
-- at all.  Read at the SECOND cascade, where the drain has something to
-- release.  Across the fold parameter the descent reads 7, 13, 19, 25,
-- 31 while the bound reads 10, 13, 16, 19, 22: six per fold layer
-- against three, TYING at depth two and crossing at depth three.  A
-- linear crossing in a parameter the bound does see.
--
-- WHAT IS PINNED HERE AND WHAT IS NOT.  The slots premise is
-- discharged by construction — the statement's vocabulary is taken to
-- be the one the run itself carries — and the payload's nesting
-- premise by computation, pinned below.  The other two are not, and
-- they fail differently.  `nestOK?` does not REDUCE in the typechecker
-- though it computes fine in native code, which is the ordinary
-- consequence of a family being sealed for cost; the harness reads it
-- true at this instant, and that is measured and not rechecked.
-- `capsOK?` computes NOWHERE — `capsAt` sits on the caps recurrence
-- and does not terminate even natively — so no witness will ever
-- discharge it.  The escape left to the statement is therefore that
-- one of those two excludes a state a real run reaches.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here touches the WIDTH form, which
-- is what the consumer actually needs and which this same instant
-- clears by two orders of magnitude.  What dies is the plan to prove a
-- per-delivery form and widen it, and with it the per-CHAIN form, whose
-- charge is smaller still at one chain.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Cascade-Deliv-Depth where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; cascadeGo; chainsOf; arrTy; arrVal)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ)

open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; progU; insF; sucGU)
open import Verify-Budget-Sufficient.Caps-Depth using (depthCascade)
open import Verify-Budget-Sufficient.Deliveries using (delivN)
open import Verify-Budget-Sufficient.Nest-Store
  using (chainsNestD; storeNestMax; nestSyn; nestOK?; nestCapAt)

prog : Closed Γ₂ natᵗ
prog = progU 3 2

slots : Slots Γ₂
slots = insF 1 2 2

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE (gasPad (sucGU 1 2 2 3 2) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the state the FIRST cascade leaves, which is where the drain has
-- something parked
after1 : Sched Γ₂ × EvalSt prog
after1 with sched-next (proj₁ sub)
... | inj₁ _        = sub
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ sub)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the second cascade's two sides, and the two premises that compute.
-- The slots premise is discharged by construction: the statement's
-- vocabulary is taken to be the one the run carries
row : ℕ × ℕ × Bool × Bool
row with sched-next (proj₁ after1)
... | inj₁ _        = 0 , 0 , false , false
... | inj₂ (a , sd) =
  let st  = proj₂ after1
      sl  = Sched.slots sd
      stL = cascadeLatch a st
      ch  = chainsOf a st
      g   = cascadeGo a 2 ch sd stL
  in depthCascade a 2 ch sd stL
   , (nestDᵛ (arrTy a) (arrVal a) + chainsNestD ch
      + storeNestMax sd stL + delivN stL (proj₂ (proj₂ g)) * nestSyn prog sl)
   , nestOK? prog sl 2 sd stL
   , (nestDᵛ (arrTy a) (arrVal a) ≤ᵇ nestCapAt prog sl 2)

-- THE FIGURES, PINNED.  Spelled out rather than left inline so that any
-- repair moving either measure fails here, naming the number, instead
-- of quietly turning the crossing into an equality
descent≡19 : proj₁ row ≡ 19
descent≡19 = refl

perDeliv≡16 : proj₁ (proj₂ row) ≡ 16
perDeliv≡16 = refl

val-hyp : proj₂ (proj₂ (proj₂ row)) ≡ true
val-hyp = refl

cascade-deliv-depth-absurd : proj₁ row ≤ proj₁ (proj₂ row) → ⊥
-- `19 ≤ᵇ 16` reduces to `false`, so `T` of it IS the empty type
cascade-deliv-depth-absurd h = ≤⇒≤ᵇ h
