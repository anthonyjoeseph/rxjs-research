-- THE CARRIED BOUND IS FALSE AT EVERY DATA TYPE, AND THE ENTRY
-- INVARIANT CANNOT REPAIR IT BECAUSE THE PROGRAM IS NOT WHAT IS WRONG.
--
-- `subscribe-carried` says a subscribe's own burst hands on nothing
-- deeper than the rank it was entered at, and it says it of EVERY value
-- the burst carries.  A value at a data type is read at nought — the
-- reading only counts written observables — so the claim at such a value
-- is `0 < r`, a demand on the ENTRY rather than a bound on the value.
-- The root enters a program with no `strmᵗ` anywhere at a rank of
-- nought, and every conjunct of the entry invariant holds there.
--
-- SO THE WITNESS IS A ONE-SHOT SOURCE OF ONE NUMERAL, WHICH IS AS FAR
-- FROM THE RISKY REGION AS A PROGRAM GETS.  Nothing here is nested,
-- shared, gated or flattened: the burst is the source's own, the value
-- is a natural, and the entry is the one the top line actually builds.
-- A statement refuted there is not a statement with a hard case.
--
-- WHAT THE REPAIR HAS TO DO IS SPLIT ON THE TYPE, AND THAT IS WHY THIS
-- IS CHEAP RATHER THAN ALARMING.  The bound exists to pay one guard —
-- the hop's, which compares an OBSERVABLE value against the rank — and
-- an observable value reaches a frame as the payload of a `strmᵗ`, the
-- one head the reading charges a successor for.  So the strictness is
-- real exactly where it is spent and vacuous everywhere else, and a
-- predicate reading the value's TYPE asks for it only where a hop can
-- follow.  Stated flat, it asks every numeral in the development to be
-- written below the rank, which is not a property of programs at all.
module Refuted.Carried-Unranked where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᵃ_)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; InstEmit; InstEvent; value)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; nat̂; ofᵉ; syncSizeᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ; obsDepthᵛ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (Stream; Path; root; Sched; EvalSt; subscribeE;
  sched-init; st-init)

----------------------------------------------------------------------
-- THE STATEMENT AND BOTH ITS PREDICATES, WRITTEN OUT HERE RATHER THAN
-- IMPORTED, exactly as every sibling witness is.  `src` declares a
-- postulate of this type over predicates of these shapes, and a
-- refutation that APPLIED either would be evidence about whatever those
-- names say today rather than about the FLAT reading it was taken
-- against.  Written out, the finding survives the repair it forces —
-- which is a repair to the predicate, so an importing witness would go
-- quiet on the day it landed and report a clean tree instead.
----------------------------------------------------------------------

FlatEntryOK : ∀ {n} {Γ : Ctx n} {u} → Closed Γ u → Tri → Set
FlatEntryOK b (_ , r , sz) = syncSizeᵉ b ≤ sz × obsDepthᵉ b ≤ r

FlatEventOK : ∀ {n} {Γ : Ctx n} {u} → Tri → InstEvent (Val Γ u) → Set
FlatEventOK {u = u} (_ , r , _) (value v) = obsDepthᵛ u v < r
FlatEventOK _ _ = ⊤

FlatBurstOK : ∀ {n} {Γ : Ctx n} {s} → Stream Γ s → Tri → Set
FlatBurstOK bs τ = All (λ em → All (FlatEventOK τ) (InstEmit.events em)) bs

SubscribeCarried : Set
SubscribeCarried =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (b : Closed Γ u) → FlatEntryOK b τ →
    (κ : Path Γ lo u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    FlatBurstOK {Γ = Γ} (proj₁ (subscribeE {e = e} ac b κ id now sched st)) τ

----------------------------------------------------------------------
-- THE PROGRAM AND THE ENTRY, AND BOTH ARE THE MACHINE'S OWN.  The
-- schedule and the store are the root seedings, and the triple's third
-- component is the term's own measure rather than a chosen numeral, so
-- the entry invariant is discharged by reflexivity in both conjuncts.
-- Nothing here is adversarial: this is the entry `evaluate` builds.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

b₀ : Closed Γ₀ natᵗ
b₀ = ofᵉ (nat̂ 1 ∷ [])

τ₀ : Tri
τ₀ = 0 , 0 , syncSizeᵉ b₀

ac₀ : Acc _≺_ τ₀
ac₀ = ≺-wellFounded τ₀

-- LOAD-BEARING, and it is the half a reader will not believe: the rank
-- the root enters at is NOUGHT, because the program writes no
-- observable anywhere and the reading counts nothing else.
root-rank : obsDepthᵉ b₀ ≡ 0
root-rank = refl

entry₀ : FlatEntryOK b₀ τ₀
entry₀ = ≤-refl , ≤-refl

----------------------------------------------------------------------
-- THE REFUTATION.  A one-shot source emits `init`, its values, a close
-- and a complete in one emit, so the burst's second event is the
-- numeral — and the claim at that position reads it strictly below
-- nought.  The pattern walks to it and the absurdity is immediate,
-- which is the whole point: no arithmetic is spent, because there is no
-- arithmetic in the finding.
----------------------------------------------------------------------

carried-false : SubscribeCarried → ⊥
carried-false h
  with h {e = b₀} ac₀ b₀ entry₀ (root {lo = 0}) 0 0
         (sched-init b₀ ins₀) (st-init b₀)
... | (_ ∷ᵃ () ∷ᵃ _) ∷ᵃ _
