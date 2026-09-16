-- THE MID-BURST SIMULATION RELATION, AND THE VOCABULARY IT IS WRITTEN
-- IN.  A subscribe frame emits its whole burst in one go, so the
-- protocol argument's first obligation is a relation that holds while
-- that burst is being built: the automaton's live multiset shadows the
-- evaluator's registry, the registry is well-typed against the
-- schedule, and the open instant — if any emit has landed — is the
-- burst's own with nothing owed.
--
-- WHY THE SHADOW IS CONDITIONED ON `dying` AND NOT STATED AT EVERY
-- SOURCE.  The all-sources form is FALSE, and not marginally: a victim
-- that has already delivered on a dying source carried its exhausted
-- close on its own emit, so the cut drops it from the registry and
-- emits no close for it.  The registry loses an entry the live list
-- never sees, and the two counts part by exactly that victim.  The
-- hypothesis is discharged at every source the machinery can serve,
-- because the cut chain is already conditioned pointwise on this same
-- predicate.
--
-- AND `dying` IS READ OFF THE EVALUATOR STATE RATHER THAN CARRIED AS AN
-- INDEX.  The fold side of this face solves the same problem by
-- excluding the arrival's own source, which needs that source as a
-- parameter; a subscribe frame has no such source, and giving this
-- relation one it does not need would put a spurious index on every
-- preservation statement above it.  The state this relation already
-- takes carries the set.
--
-- WHAT IS DELIBERATELY ABSENT, because the omission is a finding rather
-- than an economy.  Node-counter coherence is not merely inconvenient
-- mid-burst, it is FALSE there, in both directions: a flattener
-- subscribes an inner before bumping its counter, so throughout the
-- inner's burst the registrations exist while the count trails them;
-- and a take cut strips registrations without touching the count, so
-- the count leads.  No relation between the two survives both, so no
-- weakening of such a field would work — it has to be re-established
-- once, at the frame's exit, rather than threaded.  The same goes for
-- the after-completion plumbing claim: an inner base completing beside
-- a live asynchronous sibling makes it false over the whole registry,
-- and its only consumer is the root exit, so it is owed there.
--
-- RECOVERY: git show 919f115:agda/evidence/refuted/Refuted/Cut-Through.agda
module Verify-Well-Formed.Invariant where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _≤_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Source; hot; cold)
open import Rx.Exp using (Ctx; Closed; Ty; _≟ᵗ_)
open import Rx.Slots using (Slot; scripted; shared)
open import Rx.Evaluator using (EvalSt; Sched; LiveSource; RegRow; regSource;
  memberSource)
open import Rx.Protocol using (ProtocolSt; countIn)

------------------------------------------------------------------
-- THE VOCABULARY.
------------------------------------------------------------------

-- registrations of a source, counted off the registry — the writer's
-- ledger the automaton's live multiset has to shadow
countRegs : ∀ {n} {Γ : Ctx n} {t}
          → Source → List (RegRow Γ t) → ℕ
countRegs s [] = zero
countRegs s ((_ , x , _) ∷ r) =
  if s ≡ᵇ regSource x then suc (countRegs s r) else countRegs s r

sameTy : Ty → Ty → Bool
sameTy s u with s ≟ᵗ u
... | yes _ = true
... | no  _ = false

-- a registration's source-type agrees with every live entry of that
-- same source.  Share-sunk registrations whose source has no live entry
-- are unconstrained, which is sound because only a SCHEDULED source's
-- entries are ever read and those all trace to a live entry
liveTypeOK? : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveTypeOK? s u []       = true
liveTypeOK? s u (l ∷ ls) =
  (if LiveSource.source l ≡ᵇ s then sameTy u (LiveSource.elemTy l) else true)
    ∧ liveTypeOK? s u ls

regTyped? : ∀ {n} {Γ : Ctx n} {t} → List (RegRow Γ t)
          → List (LiveSource Γ) → Bool
regTyped? []                      live = true
regTyped? ((_ , s , (u , _)) ∷ r) live = liveTypeOK? (regSource s) u live ∧ regTyped? r live

-- a Bool rather than an equation on the slot's shape, so that the field
-- below needs no implicit well-formedness witness juggling: a caller
-- that has split on the slot discharges the premise by congruence
hotSlot? : ∀ {n} {Γ : Ctx n} {k t} → Slot Γ k t → Bool
hotSlot? (scripted (hot _))    = true
hotSlot? (scripted (cold _ _)) = false
hotSlot? (shared _)            = false

-- THE SCHEDULE'S OWN WELL-TYPEDNESS, named once so that the field below
-- and every preservation leaf share one spelling.  It is a FIELD rather
-- than a hypothesis because a schedule's live list and its slot table
-- are independent components, so no lemma over an arbitrary schedule
-- could be true, and a hypothesis would bind only whoever calls today
-- while making the debt invisible to the wiring law.
HotLive : ∀ {n} {Γ : Ctx n} → Sched Γ → Set
HotLive {Γ = Γ} sched = ∀ (i : Fin _) →
  hotSlot? (Sched.slots sched i) ≡ true →
  liveTypeOK? (toℕ i) (lookup Γ i) (Sched.live sched) ≡ true

------------------------------------------------------------------
-- THE RELATION.
------------------------------------------------------------------

-- AND THERE IS NO BASE-CASE LEMMA HERE, WHICH IS THE LEAF-ONLY LAW
-- DECIDING A DESIGN QUESTION RATHER THAN AN OMISSION.  The initial
-- schedule and the initial evaluator state do satisfy this relation
-- against the automaton's initial state, and the proof is five field
-- projections — but its only possible use today is as an ARGUMENT to
-- the root leaf below, since the induction that would consume it is
-- postulated.  Proven work handed to a postulate is asserted to
-- suffice and checked by nobody, so the root leaf is instead stated at
-- the initial state outright and OWES the base case inside itself.
-- The lemma lands in the commit that turns that leaf into a body.

record BurstInv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                (id : ℕ) (sched : Sched Γ) (st : EvalSt e)
                (S : ProtocolSt) : Set where
  field
    live-matches  : ∀ (s : Source) →
      memberSource s (EvalSt.dying st) ≡ false →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    reg-typed     : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low   : ProtocolSt.horizon S ≤ id
    -- subscribe and plumbing settle to net zero and a burst mints no
    -- handoff, so the open instant's owed table is LITERALLY empty
    current-frame : (ProtocolSt.current S ≡ nothing)
                  ⊎ (ProtocolSt.current S ≡ just (id , []))
    hot-live      : HotLive sched

