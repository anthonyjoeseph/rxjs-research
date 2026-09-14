-- AND THE TYPE-SPLIT READING IS FALSE TOO, AT THE ONE CLAUSE WHERE THE
-- ENTRY INVARIANT SPEAKS ABOUT A SYMBOL RATHER THAN ABOUT A PROGRAM.
--
-- `subscribe-carried` reads the term it is entered at, and a slot
-- REFERENCE is one symbol standing for a definition of any nesting: the
-- reading gives it nought, deliberately, since pricing it would need the
-- staged fixpoint a slot environment exists to carry.  So the entry
-- invariant at a reference says nothing at all, while the burst the
-- clause returns is the DEFINITION's — and the definition may write
-- observables the caller's rank cannot dominate.
--
-- THE CONNECT IS WHAT MAKES THIS SOUND FOR THE DESCENT AND UNSOUND FOR
-- THE BOUND, WHICH IS WHY IT IS WORTH SEPARATING FROM ITS SIBLING.  The
-- connect edge descends the UNCONNECTED COUNT and re-seeds the rank at
-- the definition's own nesting, so the machine is never asked to compare
-- the two and the descent is fine.  A statement about what the subscribe
-- HANDS ON is asked exactly that comparison, and has nothing to make it
-- with.
--
-- SO THE REPAIR IS A CONJUNCT ABOUT THE SCHEDULE AND NOT ABOUT THE
-- TERM.  Every sibling witness here is answered by reading the program
-- more carefully; this one cannot be, because the program is `input
-- zero` and there is nothing in it to read.  What has to be said is that
-- the slots the schedule carries are themselves written below the rank —
-- a quantifier over the telescope, which is the one thing the entry
-- invariant does not yet mention.
module Refuted.Carried-Shared where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᵃ_)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; InstEmit; InstEvent; value)
open import Rx.Exp using (Ctx; Closed; Val; Ty; natᵗ; obs; nat̂; ofᵉ; strmᵗ;
  input; syncSizeᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Strat-Order using (Tri)
open import Rx.Evaluator using (Stream; Path; root; Sched; EvalSt; subscribeE;
  sched-init; st-init)

----------------------------------------------------------------------
-- THE STATEMENT AND ITS PREDICATES, WRITTEN OUT as every sibling is —
-- and here in the TYPE-SPLIT reading its predecessor forced, so that the
-- two witnesses kill two different statements rather than one twice.
-- The value clause asks for the bound only where an observable sits,
-- which is what makes the row below a finding about the SLOT rather than
-- about the arithmetic.
----------------------------------------------------------------------

EntryOK : ∀ {n} {Γ : Ctx n} {u} → Closed Γ u → Tri → Set
EntryOK b (_ , r , sz) = syncSizeᵉ b ≤ sz × obsDepthᵉ b ≤ r

ValOK : ∀ {n} {Γ : Ctx n} (u : Ty) → Tri → Val Γ u → Set
ValOK (obs t) (_ , r , _) o = obsDepthᵉ o < r
ValOK _       _           _ = ⊤

EventOK : ∀ {n} {Γ : Ctx n} {u} → Tri → InstEvent (Val Γ u) → Set
EventOK {u = u} τ (value v) = ValOK u τ v
EventOK _ _ = ⊤

BurstOK : ∀ {n} {Γ : Ctx n} {s} → Stream Γ s → Tri → Set
BurstOK bs τ = All (λ em → All (EventOK τ) (InstEmit.events em)) bs

SubscribeCarried : Set
SubscribeCarried =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (b : Closed Γ u) → EntryOK b τ →
    (κ : Path Γ lo u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    BurstOK {Γ = Γ} (proj₁ (subscribeE {e = e} b κ id now sched st)) τ

----------------------------------------------------------------------
-- ONE SLOT, HOLDING A DEFINITION THAT WRITES AN OBSERVABLE.  The
-- telescope is the machine's own and the definition references no input,
-- so the stratification side condition discharges by unification.  What
-- the program being subscribed says is `input zero` and nothing else.
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
-- cannot dominate what the connect returns.
def-depth : obsDepthᵉ d₁ ≡ 1
def-depth = refl

ref-depth : obsDepthᵉ ref₁ ≡ 0
ref-depth = refl

-- the first component has to clear the unconnected count or the connect
-- refuses and the burst carries no value at all; one is enough, since
-- the slot being connected is struck from the count as it is taken
τ₁ : Tri
τ₁ = 1 , 0 , syncSizeᵉ ref₁

entry₁ : EntryOK ref₁ τ₁
entry₁ = ≤-refl , ≤-refl

----------------------------------------------------------------------
-- THE REFUTATION.  The connect emits the share's own registration and
-- then plumbs the definition's burst through unchanged, so the second
-- emit carries the observable the definition wrote — read against a rank
-- of nought, which no observable can be below.
----------------------------------------------------------------------

carried-shared-false : SubscribeCarried → ⊥
carried-shared-false h
  with h {e = ref₁} ref₁ entry₁ (root {lo = 1}) 0 0
         (sched-init ref₁ ins₁) (st-init ref₁)
... | _ ∷ᵃ (_ ∷ᵃ () ∷ᵃ _) ∷ᵃ _
