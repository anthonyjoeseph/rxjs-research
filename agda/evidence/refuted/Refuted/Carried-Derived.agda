-- THE SAME CROSSING, ASKED OF A DERIVATION RATHER THAN OF THE MACHINE,
-- BECAUSE THAT IS THE STATEMENT THAT IS NOW LIVE.
--
-- The claim is that a subscribe entered at a triple hands back a burst
-- whose every observable value is shallower than that triple's rank,
-- asked over `subscribeE⇓` — so the machine's totality is not in the
-- way and it can be put to a run built by hand.  What it kills is the
-- reading with NO SLOT ENVIRONMENT: a slot REFERENCE is one symbol
-- standing for a definition of any nesting, such a reading gives it
-- nought, and the connect plumbs the DEFINITION's burst out through the
-- reference's own entry.  The witness below is that run, written out
-- constructor by constructor.
--
-- AND THAT IS WHY THE MEASURE IT INSTANTIATES AT IS WRITTEN HERE RATHER
-- THAN IMPORTED.  `Rx.Obs-Depth` is parameterised over an environment
-- now, and `src` carries a nought specialisation of its own; reading
-- THAT would make this witness track whatever the specialisation comes
-- to mean, when what it is evidence about is the environment-free
-- reading as such.  `zero-env` below is the localisation, and the two
-- figures pinned by `refl` are what would fail loudly if it moved.
--
-- AND STATING IT RELATIONALLY IS WHY THIS ONE IS WORTH HAVING SEPARATELY
-- FROM ITS MACHINE-SIDE SIBLING.  A witness here dies when `src` can no
-- longer STATE what it kills, and the machine is what the cutover
-- deletes — so the sibling expires with it while the claim it kills
-- walks on into the builder unchallenged.  This one is stated in the
-- vocabulary that survives the cutover, and it imports the predicates
-- from the module the builder itself spends rather than restating them,
-- so no repair can move the statement out from under the witness
-- without moving the witness with it.
--
-- WHAT IT COSTS TO BUILD, AND IT IS WHAT MAKES THE ROW LOAD-BEARING.
-- The derivation is `subs-shared` over `slot-connect` over
-- `connect-died` over `subs-of`: every branch taken is the ordinary
-- one, the share is fresh, the definition is a one-shot, and no premise
-- anywhere is adversarial.  The one thing chosen adversarially is the
-- ENTRY, and it is chosen to be the entry the root itself builds for
-- this program.  So the failure is not reachable only down a path a run
-- avoids — it is the first thing that happens.
--
-- REFUTED: git show 80e527f9:agda/evidence/refuted/Refuted/Carried-Shared.agda
--   — the machine-side sibling, whose witness this is stated over the
--   relation.  It is at a sha because it read the machine's own
--   subscribe, which `src` no longer has.
module Refuted.Carried-Derived where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; nat̂; strmᵗ; ofᵉ; input;
  syncSizeᵉ)
open import Rx.Obs-Depth using (depᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Strat-Order using (Tri; emptyHold)
open import Rx.Evaluator using (Stream; Path; root; Sched; EvalSt;
  sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-shared; subs-of;
  slot-connect; connect-died)
open import Rx.Evaluator.Doorless using (EntryOK; BurstOK)

----------------------------------------------------------------------
-- THE STATEMENT, IMPORTED RATHER THAN RESTATED.  `EntryOK` and
-- `BurstOK` are the builder's own, so a repair that weakens either one
-- weakens this witness in the same edit instead of leaving it green
-- against a predicate nothing uses.  Only the ENVIRONMENT they are
-- read at is local, which is the one thing the repair moved.
----------------------------------------------------------------------

zero-env : ∀ {n} → Fin n → ℕ
zero-env _ = 0

BurstCarried : Set
BurstCarried =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
    {b : Closed Γ u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    EntryOK zero-env b τ →
    subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
    BurstOK zero-env burst τ

----------------------------------------------------------------------
-- ONE SLOT, HOLDING A DEFINITION THAT WRITES AN OBSERVABLE, and a
-- program that says `input zero` and nothing else.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = obs natᵗ ∷ []

d₁ : Closed Γ₁ (obs natᵗ)
d₁ = ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])

ins₁ : Slots Γ₁
ins₁ zero    = shared d₁
ins₁ (suc ())

ref₁ : Closed Γ₁ (obs natᵗ)
ref₁ = input zero

-- LOAD-BEARING, and it is the whole crossing: the definition writes one
-- level of observable while the reference standing for it reads nought,
-- so the entry invariant holds at EVERY rank including the one that
-- cannot dominate what the connect plumbs out.
derived-def-depth : depᵉ zero-env d₁ ≡ 1
derived-def-depth = refl

derived-ref-depth : depᵉ zero-env ref₁ ≡ 0
derived-ref-depth = refl

τ₁ : Tri
τ₁ = 1 , emptyHold 1 , 0 , syncSizeᵉ ref₁

entry₁ : EntryOK zero-env ref₁ τ₁
entry₁ = ≤-refl , ≤-refl

below₁ : 0 < 1
below₁ = s≤s z≤n

----------------------------------------------------------------------
-- THE REFUTATION.  The share is fresh, so the slot subscribe takes its
-- connecting branch; the definition is a one-shot, so its burst
-- completes and the connect takes its dying one; and the plumbed emit
-- carries the observable the definition wrote, read against a rank of
-- nought, which no observable can be below.
----------------------------------------------------------------------

carried-derived-false : BurstCarried → ⊥
carried-derived-false h
  with h {e = ref₁} {τ = τ₁} {b = ref₁} {κ = root {lo = 1}} {id = 0} {now = 0}
         {sched = sched-init ref₁ ins₁} {st = st-init ref₁}
         entry₁
         (subs-shared {below = below₁} refl
           (slot-connect refl refl
             (connect-died {below = below₁} (subs-of refl) refl)))
... | _ ∷ᵃ (_ ∷ᵃ () ∷ᵃ _) ∷ᵃ _
