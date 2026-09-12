-- THE REFOLD COUNT CROSSES INSIDE THE ROOT SUBSCRIBE FRAME, SO THE
-- OPERATOR LEAF IS FALSE AT THE ENTRY EVERY RUN ACTUALLY USES.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- WHERE THE DRY EMIT IS, AND IT IS THE FINDING.  The sibling witness
-- exhibits runs that go dry and locates the falsity in the seeding; it
-- runs `evaluate`, which subscribes and then drains, so nothing there
-- says which of the two emitted the marker.  This one subscribes and
-- stops.  The marker is already in the burst — at no arrival, no
-- registration, and no drain step — which puts the whole crossing
-- inside one frame, between the door and the first thing the loop does.
--
-- WHAT THAT RULES OUT, AND IT IS A WHOLE FAMILY OF REPAIRS.  Anything
-- carried BETWEEN cascades reaches this crossing too late: a field on
-- the coherence record, a strengthened fit, a count read off the entry
-- that stored an accumulator — each of them is a fact about a store
-- some earlier arrival left, and there is no earlier arrival here.  The
-- only fact in scope at the crossing is the one the door supplies, and
-- the door supplies the term's own reading.
--
-- WHY THE TERM'S READING CANNOT BE IT.  The rows below take the two
-- quantities apart on the axis that separates them.  A frame's own
-- emissions are not subterms of the term it entered on: a fold builds
-- its accumulator at RUN time, one fresh layer per refold, so the
-- carried depth climbs one per source literal.  The reading the frame is
-- entered at is BLIND to source length — the scan clause charges a power
-- of the store bound times the templates, and a literal costs nothing.
-- A linear rate against a flat one crosses, and a longer source crosses
-- any bound.
--
-- SO A REPORT ALONGSIDE THE EMISSIONS IS NOT A WEAKER OBLIGATION.  The
-- second statement below is the route that would have had the burst walk
-- carry its emissions' hop content beside them, invariant in the motive,
-- so the hop edge could spend the report instead of a fact about an
-- arbitrary inner.  It crosses at exactly the pairs the dry marker
-- crosses at — two literals under bound zero, four under bound one, and
-- holding everywhere else — which says the report and the guard are one
-- statement rather than two, and establishing the first would have been
-- establishing the second.
--
-- THE BOUNDARY.  Two bounds and four lengths, on one fold family, with a
-- merge as the only flattener; nothing here sweeps a switch or an
-- exhaust root, and the general claim — that every bound is crossed by
-- some length — is the extrapolation the sibling witness already records
-- as one.
module Refuted.Root-Refold where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _⊔_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; m≤m+n; ≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Fin using (Fin)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  subst)

open import Rx.Prim using (Id; Tick; Source; InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; nat̂; ofᵉ; scanᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE; root;
  rootTri; rootWitness; sched-init; st-init; hasDry; unconn)
open import Verify-Rank-Sufficient.Dry using (opShape)

open import Refuted.Sync-Count using (Γ₀; ins₀; step; liveSeed; prog₂)

----------------------------------------------------------------------
-- THE LEAF, WRITTEN OUT HERE RATHER THAN IMPORTED, invariant and all,
-- so that this is evidence about the form it was taken against: a
-- repair that adds a conjunct makes the witness below fail to typecheck
-- rather than quietly agree with it.  The triple and its accessibility
-- proof are the machine's OWN — `rootTri` is what `evaluate` seeds a
-- root subscribe with — so nothing here is a hand-picked entry, which is
-- the whole difference from the sibling that killed the two-conjunct
-- form.
----------------------------------------------------------------------

EntryReads₃ : ∀ {n} {Γ : Ctx n} {u} →
              ℕ → Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads₃ V (U , R , s) o sl cs =
  unconn sl cs ≤ U × hopDᵉ V (slotHop V sl) o ≤ R × syncSizeᵉ o ≤ s

DryOperator : Set
DryOperator = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
  (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → opShape o ≡ true →
  EntryReads₃ (Sched.storeBound sched) τ o
    (Sched.slots sched) (EvalSt.connectedShares st) →
  hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

----------------------------------------------------------------------
-- THE RUN, AND IT STOPS AT THE DOOR.  `burstAt` is `evaluate`'s own root
-- entry with the drain removed: the same seed, the same bound, the same
-- initial store, and nothing after the subscribe returns.
----------------------------------------------------------------------

burstAt : ∀ {n} {Γ : Ctx n} {t} (V : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
          Stream Γ t
burstAt V e ins =
  proj₁ (subscribeE (rootWitness V e ins) e root 0 0 (sched-init V e ins)
          (st-init e))

opShape-prog₂ : opShape prog₂ ≡ true
opShape-prog₂ = refl

-- the invariant at the machine's own seed, and every conjunct is
-- reflexivity up to the unit the root adds: nothing has been connected,
-- nothing stored, nothing delivered
reads₂ : EntryReads₃ 0 (rootTri 0 prog₂ ins₀) prog₂
           (Sched.slots (sched-init 0 prog₂ ins₀))
           (EvalSt.connectedShares (st-init prog₂))
reads₂ = ≤-refl , m≤m+n (hopDᵉ 0 (slotHop 0 ins₀) prog₂) 0 , ≤-refl

-- LOAD-BEARING, and it is the row the whole file is built around: the
-- marker is in the SUBSCRIBE burst, so no fact about a store an earlier
-- cascade left can be what repairs this
dry₂ : hasDry (burstAt 0 prog₂ ins₀) ≡ true
dry₂ = refl

dry-operator-root-false : DryOperator → ⊥
dry-operator-root-false h
  with trans (sym (h (rootWitness 0 prog₂ ins₀) prog₂ root 0 0
                     (sched-init 0 prog₂ ins₀) (st-init prog₂)
                     opShape-prog₂ reads₂))
             dry₂
... | ()

----------------------------------------------------------------------
-- THE READING, over the values a frame hands out.  Only a `value` is a
-- carrier: an `init` or a `close` carries no payload to subscribe, so a
-- bound refuted off one would be refuted off nothing.  The join rather
-- than the sum, because the claim is about how deep a single carrier can
-- be and not about how many there are.
----------------------------------------------------------------------

evHop : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) →
        List (InstEvent (Closed Γ u)) → ℕ
evHop V η []             = 0
evHop V η (value v ∷ es) = hopDᵉ V η v ⊔ evHop V η es
evHop V η (_ ∷ es)       = evHop V η es

carried : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) →
          Stream Γ (obs u) → ℕ
carried V η []         = 0
carried V η (em ∷ ems) = evHop V η (InstEmit.events em) ⊔ carried V η ems

WalkCarry : Set
WalkCarry = ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (e : Closed Γ (obs u))
            (ins : Slots Γ) →
            carried V (slotHop V ins) (burstAt V e ins)
              ≤ hopDᵉ V (slotHop V ins) e

----------------------------------------------------------------------
-- THE FAMILY, which is the sibling's fold with its root flattener
-- stripped, so the emissions measured are the frame's OWN and a claim
-- about what a walk reports is not taken one hop above where the walk
-- makes it.  Four sources differing in literals alone.
----------------------------------------------------------------------

inner₁ inner₂ inner₃ inner₄ : Closed Γ₀ (obs natᵗ)
inner₁ = scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ []))
inner₂ = scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))
inner₃ = scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ []))
inner₄ = scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

η : (V : ℕ) → Fin 0 → ℕ
η V = slotHop V ins₀

----------------------------------------------------------------------
-- THE RANK THE FRAME IS ENTERED AT, AND IT DOES NOT MOVE WITH THE
-- SOURCE.  Each row is LOAD-BEARING: a reading that grew with the
-- literals would say the emitter is charged for what it folds over, and
-- the crossings below would then be a question of rates rather than of
-- blindness.  It grows with the BOUND and with nothing else.
----------------------------------------------------------------------

_ : hopDᵉ 0 (η 0) inner₄ ≡ 1                           -- LOAD-BEARING
_ = refl

_ : hopDᵉ 1 (η 1) inner₄ ≡ 3                           -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CARRIED DEPTH, AND IT COUNTS THE REFOLDS.  Each row is
-- LOAD-BEARING and could have failed in either direction: a depth that
-- stalled would say the step does not re-wrap what it is handed, and one
-- that multiplied would say a refold costs more than the single merge
-- layer the step writes.  It adds one per literal at both bounds — the
-- rate is the run's, and the bound does not enter it.
----------------------------------------------------------------------

_ : carried 0 (η 0) (burstAt 0 inner₁ ins₀) ≡ 1        -- LOAD-BEARING
_ = refl

_ : carried 0 (η 0) (burstAt 0 inner₂ ins₀) ≡ 2        -- LOAD-BEARING
_ = refl

_ : carried 1 (η 1) (burstAt 1 inner₂ ins₀) ≡ 2        -- LOAD-BEARING
_ = refl

_ : carried 1 (η 1) (burstAt 1 inner₃ ins₀) ≡ 3        -- LOAD-BEARING
_ = refl

_ : carried 1 (η 1) (burstAt 1 inner₄ ins₀) ≡ 4        -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CROSSING, pinned by `refl` outside the ⊥ so that it moves visibly
-- if either side does.  It is taken at bound ONE rather than at zero, so
-- nothing here rests on a degenerate allowance: four against three, one
-- literal past the length that fits — and the row directly above it is
-- the TIGHT one, three against three, which is what says the guard is
-- deciding on the length and not on the family.
----------------------------------------------------------------------

cross₁₄ : (carried 1 (η 1) (burstAt 1 inner₄ ins₀)
            ≤ᵇ hopDᵉ 1 (η 1) inner₄) ≡ false           -- LOAD-BEARING
cross₁₄ = refl

walk-carry-false : WalkCarry → ⊥
walk-carry-false h = subst T cross₁₄ (≤⇒≤ᵇ (h 1 inner₄ ins₀))
