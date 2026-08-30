-- ══════════════════════════════════════════════════════════════════
-- A DEFER PARKS ITS BODY AT FULL SYNTAX SIZE, AND THE NEST FACE'S
-- PREMISES ARE ALL SYNC-DENOMINATED, so no fixed-cap caps-preservation
-- statement over that vocabulary survives the defer clause.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  The caps-preservation walk family: from a
-- slots pin, the invariant, `nestValOK?`, `nestClosOK?` and a `descW`
-- descent bound, `subscribeE` returns a state at the same slots that
-- still satisfies `nestCapsOK?`.
--
-- WHY IT LOOKED RIGHT.  Every write the walk performs is a `setNode`
-- of a width-checked node or a mint that the predicate does not read,
-- and the per-instant step theorem covering the thru boundary is
-- proven.  The probe rows -- merge, switch, exhaust heads, shared
-- variants, multi-instant -- are all green.
--
-- WHERE IT BREAKS.  `nestCapsOK?` carries `nestStB?`, which bounds
-- every pending payload by `sizeᵛ` -- FULL syntax size, counting under
-- defers.  The `deferᵉ` clause parks its own body as a pending
-- payload, and both premises that price the subscribed value --
-- `nestValOK?` (`syncSizeᵛ`) and `nestClosOK?` (`closSizeᵉ`) -- read a
-- defer as 1: the gate that makes the body free to the sync measures
-- is exactly what hides it from every premise.  So a defer over a
-- large body satisfies the whole telescope while the exit state's new
-- live entry fails `boundedLive` outright.  The proven caps-face twin
-- pays this entry from `suc (sizeᵉ b) ≤ ops`, a FULL-size budget the
-- nest face deliberately does not carry -- and at a FIXED cap even
-- that premise would not recurse through `unfoldμ`, which grows
-- `sizeᵉ`.  The size conjunct is also spent by nothing in the nest
-- walk: it is plumbing inherited from `capsOK?⇒nest`.
--
-- THE WITNESS is `deferᵉ (ofᵉ (natsD 3))` at `cSize 2` in the empty
-- context, at its own descent bound, straight from the evaluator's
-- initial state: `syncSizeᵉ` and `closSizeᵉ` of the defer are both 1,
-- and the parked body's `sizeᵉ` is 4.
--
-- WHAT DIES AND WHAT DOES NOT.  This statement of the family dies, and
-- with it the size conjunct of every fixed-cap exit statement over the
-- same premises -- the thru-step inner leaves share the shape.  The
-- width conjuncts are untouched: nothing here reaches them, and the
-- repair the numbers point at is a `nestCapsOK?` that carries only
-- what the nest measures read -- the two width conjuncts.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Defer-Park-Size where

open import Data.Bool using (Bool; true; _∧_)
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
open import Verify-Budget-Sufficient.Measures using (boundedLive)
open import Data.Bool.ListAction using (all)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestCapsOK?)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Refuted.Demand-Programs using (Γ₀; ins₀; natsD)

-- the predicate as it stood: the full-size pending bound conjoined
-- onto the two width conjuncts `nestCapsOK?` still carries
oldOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
       → Caps → Sched Γ → EvalSt e → Bool
oldOK? c sched st =
  all (boundedLive (Caps.cSize c)) (Sched.live sched)
  ∧ nestCapsOK? c sched st

-- the statement of `subscribeE-caps-exit` as it stood
Stmt : Set
Stmt = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas) (o : Closed Γ u)
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  oldOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  nestClosOK? c sl o ≡ true →
  descW g o κ id now sched st ≤ W →
  let r = subscribeE g o κ id now sched st in
  (Sched.slots (proj₁ (proj₂ r)) ≡ sl)
  × (oldOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

prog : Closed Γ₀ natᵗ
prog = deferᵉ (ofᵉ (natsD 3))

defer-park-size-absurd : Stmt → ⊥
defer-park-size-absurd s
  with proj₂ (s (caps 2 5 1) ins₀
                (descW g0 prog root 0 0 (sched-init prog ins₀) (st-init prog))
                g0 prog root 0 0 (sched-init prog ins₀) (st-init prog)
                refl refl refl refl ≤-refl)
... | ()
