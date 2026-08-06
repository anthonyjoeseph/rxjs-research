-- REFUTATION OF burst-done-false (Verify-Well-Formed.agda:1109)
--
-- The postulate claims:
--
--   burst-done-false : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
--     (id : Id) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
--     BurstInv id sched st S →
--     ProtocolSt.done S ≡ false
--
-- VERDICT: FALSE.  BurstInv carries exactly four fields:
--   live-matches  — registry/live multiset coherence
--   reg-typed     — each registry entry's type matches its live slot
--   horizon-low   — ProtocolSt.horizon S ≤ id
--   current-frame — current is nothing or just (id , [])
--
-- NONE of the four fields constrain ProtocolSt.done.  The postulate's
-- own comment (VWF:1108) concedes: "SUSPECT: true only at the right walk
-- position, not from BurstInv alone."
--
-- THE ADVERSARIAL WITNESS:
--   id    = 0
--   Γ     = Ctx 0 (empty context)
--   e     = emptyᵉ
--   sched = sched-init emptyᵉ (λ ())   — no slots, live = []
--   st    = st-init emptyᵉ             — registry = []
--   S     = record { live = [] ; horizon = 0 ; current = nothing ; done = TRUE }
--
--   BurstInv fields at this triple:
--     live-matches s : countIn s [] ≡ countRegs s []
--                    = zero ≡ zero   by refl (both return zero on [])
--     reg-typed      : regTyped? [] [] ≡ true
--                    = true ≡ true   by refl (first clause of regTyped?)
--     horizon-low    : 0 ≤ 0         by z≤n
--     current-frame  : nothing ≡ nothing  by inj₁ refl
--
-- ALL FOUR FIELDS HOLD.  The record typechecks.  Applying burst-done-false
-- then yields true ≡ false, which is ⊥ by absurd pattern matching.
--
-- THE SOURCE ALREADY KNEW.  VWF:876-882 — 230 lines ABOVE the postulate's
-- own declaration, in oneShotBurst-wf's header — states the refutation as
-- settled fact:
--
--     "the clause owes exactly ONE thing from the surrounding context, the
--      premise `deq`: `done S ≡ false` at subscribe time ... This is a
--      subscribe-TIME fact, not a frame-exit one (done may be true at exit),
--      SO BurstInv CANNOT CARRY IT; it must come from the walk order."
--
-- `burst-done-false` asserts exactly what that comment says is impossible.
-- It was a placeholder for the walk-order plumbing, not a derivable fact.
--
-- THE FIX — and it is NOT "add a trivial hypothesis".  Two claims that look
-- plausible are both FALSE, and cost a build each to discover:
--
--   (a) "The consumers already supply `done ≡ false`."  They do not.  The
--       consumers are subscribeE-wf's ofᵉ (VWF:3390) and emptyᵉ (VWF:3396)
--       clauses, and `burst-done-false` exists precisely BECAUSE they have
--       nothing else to hand `oneShotBurst-wf`'s `deq` premise.  Circular.
--   (b) "`nodry` supplies it."  It does not.  `nodry : hasDry ... ≡ false`
--       is a DIFFERENT proposition from `ProtocolSt.done S ≡ false` — the
--       dry-burst flag, not the protocol's completion latch.
--
-- The real repair is a SIGNATURE change: `subscribeE-wf` must TAKE
-- `ProtocolSt.done S ≡ false` as a premise and thread it, and
-- `burst-done-false` is then DELETED rather than restated.
--
-- Why threading is sound (the spine argument, to be checked before landing):
-- a subscribe walk is a SPINE, not a tree — mapᵉ/scanᵉ/takeᵉ/deferᵉ/μᵉ each
-- recurse into ONE child carrying S UNCHANGED, and there is no binary static
-- merge (VWF:3823: `merge(a,b)` desugars to `mergeAll(of(a,b))`, whose inners
-- are subscribed in later cascades, not in this walk).  So S is untouched
-- from walk entry until the single base burst at the spine's end, and
-- `done ≡ false` at entry survives to the base.  This matters because
-- oneShotBurst-run LATCHES done ≡ true — if a walk could subscribe two bases
-- in sequence, the second would need done ≡ false against a true latch and
-- the threaded hypothesis would itself be false.
--
-- The open question the repair must answer is therefore at the CALLERS of
-- subscribeE-wf: does each have `done ≡ false` in scope?
--
-- BUILD: cd agda && agda -i src -i probe probe/Battery-Burst-Done.agda
------------------------------------------------------------------------
module Battery-Burst-Done where

open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     using (Vec) renaming ([] to []ᵛ)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Id)
open import Rx.Exp       using (Ctx; Closed; Ty; natᵗ; emptyᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Slots; sched-init; st-init)
open import Rx.Protocol  using (ProtocolSt; protocol-init)

open import Verify-Well-Formed
  using (BurstInv; burst-done-false; countRegs)

------------------------------------------------------------------------
-- The minimal world: empty context, no slots
------------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

sched₀ : Sched Γ₀
sched₀ = sched-init e₀ ins₀

st₀ : EvalSt e₀
st₀ = st-init e₀

------------------------------------------------------------------------
-- The adversarial ProtocolSt: identical to protocol-init except done = true
------------------------------------------------------------------------

S-done-true : ProtocolSt
S-done-true = record { live = [] ; horizon = 0 ; current = nothing ; done = true }

------------------------------------------------------------------------
-- The adversarial BurstInv at done = true
-- Each field checked by refl / z≤n / inj₁ refl — .done is untouched.
------------------------------------------------------------------------

binv-done-true : BurstInv 0 sched₀ st₀ S-done-true
binv-done-true = record
  { live-matches  = λ s → refl    -- countIn s [] = zero = countRegs s []
  ; reg-typed     = refl          -- regTyped? [] [] = true
  ; horizon-low   = z≤n           -- 0 ≤ 0
  ; current-frame = inj₁ refl    -- nothing ≡ nothing
  }

------------------------------------------------------------------------
-- THE REFUTATION
-- burst-done-false applied to binv-done-true must produce
-- ProtocolSt.done S-done-true ≡ false, i.e. true ≡ false.
-- That is absurd: () pattern.
------------------------------------------------------------------------

burst-done-false-absurd : (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false) → ⊥
burst-done-false-absurd h
  with h {e = e₀} 0 sched₀ st₀ S-done-true binv-done-true
... | ()
