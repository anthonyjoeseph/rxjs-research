-- ══════════════════════════════════════════════════════════════════
-- A DEFER PARKS ITS BODY AT FULL FRAME WIDTH TOO, so the width-only
-- caps-preservation family still dies at the same clause until it
-- carries the parked-width premise the proven caps-face twin carries.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  `Refuted.Defer-Park-Size`'s statement with
-- the size conjunct already shed: from the slots pin, the two-width
-- invariant, `nestValOK?`, `nestClosOK?` and a `descW` bound,
-- `subscribeE` preserves the invariant.
--
-- WHERE IT BREAKS.  `widLive` bounds every pending payload by `pWᵛ`,
-- and the payload the defer clause parks is its own body, whose
-- delivered width (`outWᵉ` of a one-shot is its LENGTH) no premise
-- sees: the sync-size and closure premises read the defer as 1, and
-- `descW` bounds a descent that never opens a parked body.  The twin
-- pays this entry from its `dWᵉ n sl b ≤ cWid` premise -- the parked
-- width, which at a defer head is exactly the body's `pWᵉ` -- and that
-- premise is the repair here: unlike the size budget it recurses at a
-- FIXED cap, because parking is the one place width crosses a tick.
--
-- THE WITNESS is the same program as the size refutation at `cWid 1`:
-- the parked one-shot delivers three values, so its `pWᵛ` is 3.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Defer-Park-Width where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; ofᵉ; deferᵉ)
open import Rx.Prim using (Gas; g0; Id; Tick)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; Path)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Data.Bool using (Bool; _∧_)
open import Data.Bool.ListAction using (all)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?; widLive)
open import Verify-Budget-Sufficient.Nest-Walk using (nestCapsOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Refuted.Demand-Programs using (Γ₀; ins₀; natsD)

-- the predicate as it stood: the pending-width bound over the live
-- list conjoined onto the nodes conjunct `nestCapsOK?` still carries
oldWOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Caps → Sched Γ → EvalSt e → Bool
oldWOK? c sched st =
  all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched)
  ∧ nestCapsOK? c sched st

-- the statement of `subscribeE-caps-exit` as it stood
StmtW : Set
StmtW = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas) (o : Closed Γ u)
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  oldWOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  nestClosOK? c sl o ≡ true →
  descW g o κ id now sched st ≤ W →
  let r = subscribeE g o κ id now sched st in
  (Sched.slots (proj₁ (proj₂ r)) ≡ sl)
  × (oldWOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

progW : Closed Γ₀ natᵗ
progW = deferᵉ (ofᵉ (natsD 3))

defer-park-width-absurd : StmtW → ⊥
defer-park-width-absurd s
  with proj₂ (s (caps 5 1 1) ins₀
                (descW g0 progW root 0 0 (sched-init progW ins₀) (st-init progW))
                g0 progW root 0 0 (sched-init progW ins₀) (st-init progW)
                refl refl refl refl ≤-refl)
... | ()
