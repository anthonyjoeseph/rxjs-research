-- ══════════════════════════════════════════════════════════════════
-- THE SUBSCRIBE SIDE AT ONE `nestSyn` IS FALSE, and the width term it
-- was going to be a widening of is therefore load-bearing after all.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A subscribe's nesting descent, bounded by
-- its subject, its rootward path, the store it starts from, and ONE
-- `nestSyn` — one slot-vocabulary's worth of nesting, the term that pays
-- for `depthConn` descending into a slot definition the subject clause
-- weighs at zero.
--
-- WHY IT LOOKED RIGHT, AND THIS IS THE PART WORTH KEEPING.  Every edge
-- of the subscribe walk trades subject for path EXACTLY: a `mapᵉ` moves
-- `nestDᵗ f` from the subject to the path, a `*All` moves the `suc` that
-- `pathNestD` charges at `thru-outer` and nowhere else, and a `scanᵉ`
-- leaves `nestDᵗ z` spare to cover the node it installs.  Read edge by
-- edge the bound is an equality, which is why one `nestSyn` reads as
-- sufficient and why the width factor read as slack.
--
-- WHERE IT BREAKS.  `depthFinC` spends a second `suc` — concat's drain
-- runs as a WALK under the finishing frame — and that frame is a
-- `from-inner`, which `pathNestD` charges NOTHING for.  So the drain's
-- level has no path term to come out of, and the only place left is the
-- single `nestSyn`.  One `nestSyn` pays for one such level.  A program
-- whose folds nest can spend arbitrarily many.
--
-- THE WITNESS is `progU 5 2` — concatAll over three queued inners, so
-- the drain actually fires, under a fold of depth 5 — at the two-slot
-- vocabulary `insT 1 2 0`, read at the root subscribe.  Measured across
-- the fold parameter the descent reads 4, 5, 9, 13, 17, 21 while the
-- bound reads 9, 11, 13, 15, 17, 19: the descent climbs about four per
-- fold layer against the bound's flat two, TIES at depth 4, and crosses
-- at depth 5.  A linear crossing in a parameter the bound does see, not
-- a degenerate corner.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here touches the WIDTH form, which
-- is the statement the caps face actually consumes and which the same
-- witness clears with three orders of magnitude to spare — 21 against
-- 1339.  What died is the claim that the width factor was decoration
-- over a narrow truth, and with it the plan to prove the narrow form and
-- widen.  The width form is a primitive statement again.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Depth-One where

open import Data.Nat  using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Evaluator using (Sched; EvalSt; Path; sched-init; st-init; root; budgetAt)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; progU; insT)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Nest-Store
  using (pathNestD; storeNestMax; nestSyn)
open import Rx.Nest-Depth using (nestDᵉ)

-- the crossing point: concat's drain under five nested folds
prog : Closed Γ₂ natᵗ
prog = progU 5 2

slots : Slots Γ₂
slots = insT 1 2 0

sd : Sched Γ₂
sd = sched-init prog slots

st : EvalSt prog
st = st-init prog

-- pinned rather than written inline at both uses: `root` leaves its
-- indices to be solved, and the measure's use alone does not fix them
κ : Path Γ₂ natᵗ natᵗ
κ = root

-- the descent, and the bound it was claimed to sit under
descent : ℕ
descent = depthE (budgetAt prog slots 0) prog κ 0 0 sd st

oneSyn : ℕ
oneSyn = nestDᵉ prog + pathNestD κ + storeNestMax sd st + nestSyn prog slots

-- THE FIGURES, PINNED.  Spelled out rather than left inline so that any
-- repair moving either measure fails here, naming the number, instead of
-- quietly turning the crossing into an equality.
descent≡21 : descent ≡ 21
descent≡21 = refl

oneSyn≡19 : oneSyn ≡ 19
oneSyn≡19 = refl

nest-one-syn-absurd : descent ≤ oneSyn → ⊥
-- `descent ≤ᵇ oneSyn` reduces to `false`, so `T` of it IS the empty type
nest-one-syn-absurd h = ≤⇒≤ᵇ h
