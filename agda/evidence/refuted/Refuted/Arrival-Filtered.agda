-- NARROWING THE REGISTRY READING TO THE CHAINS ONE ARRIVAL REACHES, AND
-- SEEDING IT AT THAT ARRIVAL'S OWN VALUE, BUYS NOTHING.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHAT THIS TESTS, AND WHY IT LOOKED LIKE THE REPAIR.  A sibling witness
-- kills the arrival's seed against the WHOLE registry read at the
-- payload zero, and the reading it kills is doubly pessimistic in a way
-- that reading alone cannot see.  It prices every chain the registry
-- holds, including the ones this arrival's source and element type do
-- not reach; and it prices each of them against an arbitrarily deep
-- value rather than against the one actually arriving.  Both are exactly
-- the information a drain step HAS — the evaluator filters by
-- `chainsOf` before descending, and the value is in the arrival — so
-- narrowing the left side to what the step really spends is the obvious
-- next candidate, and it is strictly smaller than the refuted one.

-- IT DIES AT THE SAME TWO PROGRAMS AND BY THE SAME CROSSING.  Neither
-- narrowing does any work at the state that matters.  The FILTER does
-- not, because the deep chain is the one this arrival reaches: the
-- filtered list is a single chain and its reading is the whole
-- registry's.  The SEED does not, because the value arriving one step in
-- reads zero — the payload that was deep at the door is the one already
-- spent.  So the left side lands on the number the sibling witness
-- already refuted, against a right side that has collapsed onto the
-- term's own reading.

-- AND IT IS A RATE HERE TOO, which is what rules out reading the
-- failure as slack.  One more flattener over the same late outer takes
-- the filtered spend to three against the same right side of one, so no
-- constant added to either end repairs both programs.

-- WHAT IS DEAD IS THE PARADIGM OF READING A REGISTRY AT ALL.  Four
-- candidates now — the term, the widest state join, the arrival's seed,
-- and this, the narrowest reading a step could justify — and the last is
-- a sub-case of the third, so the sequence has stopped subdividing a
-- region and started confirming a mechanism.  A chain's reading prices
-- what its frames COULD spend, because a flattener charges a hop per
-- outer frame whether or not the descent re-enters there; what a step
-- spends is what each FRAME gives back on the payload it is handed, and
-- that is a per-template obligation rather than a reading of a list.
module Refuted.Arrival-Filtered where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _+_; _≤_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; obs; strmᵗ; ofᵉ; mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; ε; mapStep; flatten; hopOf; depthᵉ; depthᵛ; rdᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; RegId; AtFloor; Sched; EvalSt; Arrival;
  root; share-sink; _↠_; map-f; scan-f; take-f; from-inner; thru-outer;
  arrTy; arrVal; chainsOf; cascade; sched-next; subscribeE; rootWitness;
  sched-init; st-init; stHop)

----------------------------------------------------------------------
-- THE CURRENCY, WRITTEN OUT HERE RATHER THAN IMPORTED.  A repair that
-- changed what a chain's frames are priced at must make these rows fail
-- by name rather than quietly agree with them.  The seed is the shape
-- the evaluator mints an arrival's witness at: one literal over the
-- value's own reading.
----------------------------------------------------------------------

chainRd′ : ∀ {n} {Γ : Ctx n} {lo s t} (ψ : Fin n → Rd₃) →
           Path Γ lo s t → Rd₃ → Rd₃
chainRd′ ψ root                    p = p
chainRd′ ψ (share-sink i _)        p = p
chainRd′ ψ (map-f fn ↠ κ)          p = chainRd′ ψ κ (mapStep ψ ε p fn)
chainRd′ ψ (scan-f fn nid ↠ κ)     p = chainRd′ ψ κ (mapStep ψ ε p fn)
chainRd′ ψ (take-f nid ↠ κ)        p = chainRd′ ψ κ p
chainRd′ ψ (from-inner op a i ↠ κ) p = chainRd′ ψ κ p
chainRd′ ψ (thru-outer op nid ↠ κ) p = chainRd′ ψ κ (flatten p)

arrRd′ : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) → Arrival Γ → Rd₃
arrRd′ ψ a = 1 , rdᵛ ψ (arrTy a) (arrVal a)

pathsSpend′ : ∀ {n} {Γ : Ctx n} {t} (ψ : Fin n → Rd₃) →
              (a : Arrival Γ) → List (RegId × AtFloor Γ (arrTy a) t) → ℕ
pathsSpend′ ψ a []                 = 0
pathsSpend′ ψ a ((_ , _ , c) ∷ cs) =
  hopOf (chainRd′ ψ c (arrRd′ ψ a)) ⊔ pathsSpend′ ψ a cs

----------------------------------------------------------------------
-- THE TWO SIDES, READ AT THE SCHEDULE'S NEXT ARRIVAL — that is the one
-- the drain is about to serve.  The right side is the sibling witness's
-- own, unchanged, so the two statements differ in the LEFT alone and
-- this one is the smaller.  With no arrival pending there is nothing to
-- spend and the term's own reading is granted, so the statement is
-- trivially true there and the crossing cannot come from that arm.
----------------------------------------------------------------------

spend : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
spend (sched , st) with sched-next sched
... | inj₁ _       = 0
... | inj₂ (a , _) = pathsSpend′ (slotRd (Sched.slots sched)) a (chainsOf a st)

grant : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Sched Γ × EvalSt e → ℕ
grant e (sched , st) with sched-next sched
... | inj₁ _       = depthᵉ (slotRd (Sched.slots sched)) e
... | inj₂ (a , _) =
  depthᵉ (slotRd (Sched.slots sched)) e
  + (depthᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a)
     ⊔ stHop (slotRd (Sched.slots sched)) st)

FilteredFits′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) →
                Sched Γ × EvalSt e → Set
FilteredFits′ e p = spend p ≤ grant e p

----------------------------------------------------------------------
-- ONE ARRIVAL, TAKEN THROUGH THE DRAIN'S OWN STEP — the same
-- `sched-next` and the same `cascade`, in the same order — so the pair
-- it hands back is the pair the drain would have recursed on, never a
-- state written by hand.
----------------------------------------------------------------------

stepOnce : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Sched Γ × EvalSt e → Sched Γ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

FilteredPreserved : Set
FilteredPreserved = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
  (nextId : Id) (p : Sched Γ × EvalSt e) →
  FilteredFits′ e p → FilteredFits′ e (stepOnce nextId p)

----------------------------------------------------------------------
-- THE PROGRAMS, WHICH ARE THE SIBLING WITNESS'S TWO.  One slot,
-- scripted with values arriving well past the tick a gate's body is
-- scheduled on, so the gate has closed over its flattener by the time
-- anything is delivered.  `q₁` is a flattener whose outer is a gate,
-- behind a second gate; `q₃` is the same with one more flattener over
-- the same late outer.  Reused deliberately: a narrowing is refuted by
-- the witness it was proposed against, not by a new one.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 3 , 5 ∷ after 4 , 6 ∷ after 5 , 7 ∷ []))

obsSlot : ∀ {Δᵍ Δ} → Exp Γ₁ Δᵍ Δ [] (obs natᵗ)
obsSlot = ofᵉ (strmᵗ (input zero) ∷ [])

obsSlot² : ∀ {Δᵍ Δ} → Exp Γ₁ Δᵍ Δ [] (obs (obs natᵗ))
obsSlot² = ofᵉ (strmᵗ (ofᵉ (strmᵗ (input zero) ∷ [])) ∷ [])

q₁ : Closed Γ₁ natᵗ
q₁ = deferᵉ (mergeAllᵉ nothing (deferᵉ obsSlot))

q₃ : Closed Γ₁ natᵗ
q₃ = deferᵉ (mergeAllᵉ nothing (mergeAllᵉ nothing (deferᵉ obsSlot²)))

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Sched Γ × EvalSt e
entry {n = n} e ins =
  let (_ , sched , st) =
        subscribeE {lo = n} (rootWitness e ins) e root 0 0
          (sched-init e ins) (st-init e)
  in sched , st

payRd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
payRd (sched , st) with sched-next sched
... | inj₁ _       = 0
... | inj₂ (a , _) = depthᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a)

reached : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
reached (sched , st) with sched-next sched
... | inj₁ _       = 0
... | inj₂ (a , _) = length (chainsOf a st)

----------------------------------------------------------------------
-- THE CROSSING.  The entry rows are what make this a refutation of
-- PRESERVATION rather than a second witness at the door: the narrowed
-- statement HOLDS there, exactly, and one arrival takes it to two
-- against one.
----------------------------------------------------------------------

e₁ s₁ : Sched Γ₁ × EvalSt q₁
e₁ = entry q₁ insLate
s₁ = stepOnce 1 e₁

-- LOAD-BEARING: the narrowed statement is satisfiable at the door, so
-- the ⊥ below cannot be read as an entry failure the premise inherits.
-- It holds TIGHTLY, which is itself the finding the entry rows carry:
-- the narrowing buys nothing even where the statement is true
spend-e₁ : spend e₁ ≡ 3
spend-e₁ = refl

grant-e₁ : grant q₁ e₁ ≡ 3
grant-e₁ = refl

fit-e₁ : FilteredFits′ q₁ e₁
fit-e₁ = s≤s (s≤s (s≤s z≤n))

-- LOAD-BEARING: one arrival later the spend exceeds the grant, and the
-- two rows below say WHY neither narrowing did any work there
spend-s₁ : spend s₁ ≡ 2
spend-s₁ = refl

grant-s₁ : grant q₁ s₁ ≡ 1
grant-s₁ = refl

-- LOAD-BEARING: the FILTER bought nothing — the arrival reaches exactly
-- one chain and that chain is the deep one, so the filtered reading is
-- the whole registry's.  A repair that filtered harder would move this
-- row
reached-s₁ : reached s₁ ≡ 1
reached-s₁ = refl

-- LOAD-BEARING: and the SEED bought nothing — the value arriving here
-- reads zero, so seeding the walk at it is seeding it at the floor.  A
-- repair that read the payload differently would move this row
payload-s₁ : payRd s₁ ≡ 0
payload-s₁ = refl

-- LOAD-BEARING, AND IT IS ABOUT THE OTHER SIDE.  The grant already
-- carries the store — the arrival's witness is seeded at the JOIN of
-- the payload's reading with it — and here it reads NOUGHT, so the
-- right side has collapsed onto the term's own figure and there is
-- nothing for a state-carried quantity to have covered.  A repair that
-- widened the grant with anything the state holds would move this row;
-- nothing that reprices the LEFT can.
store-s₁ : stHop (slotRd insLate) (proj₂ s₁) ≡ 0
store-s₁ = refl

term-q₁ : depthᵉ (slotRd insLate) q₁ ≡ 1
term-q₁ = refl

filtered-preserved-false : FilteredPreserved → ⊥
filtered-preserved-false h with h q₁ 1 e₁ fit-e₁
... | s≤s ()

----------------------------------------------------------------------
-- AND THE GAP IS A RATE.  One more flattener over the same late outer
-- leaves the grant at one and takes the spend to three, so a fixed
-- slack added to either end repairs neither program.  These rows are
-- pinned rather than spent: the ⊥ is already had, and what they buy is
-- that it is not an off-by-one.
----------------------------------------------------------------------

e₃ s₃ : Sched Γ₁ × EvalSt q₃
e₃ = entry q₃ insLate
s₃ = stepOnce 1 e₃

-- LOAD-BEARING: the deeper program's door is tight in the same way, so
-- the collapse below is not the entry being looser or tighter
spend-e₃ : spend e₃ ≡ 4
spend-e₃ = refl

grant-e₃ : grant q₃ e₃ ≡ 4
grant-e₃ = refl

-- LOAD-BEARING, AND THIS IS THE RATE: the same one arrival takes this
-- spend to THREE against the same grant of one, so the gap grows with
-- the program
spend-s₃ : spend s₃ ≡ 3
spend-s₃ = refl

grant-s₃ : grant q₃ s₃ ≡ 1
grant-s₃ = refl

reached-s₃ : reached s₃ ≡ 1
reached-s₃ = refl

payload-s₃ : payRd s₃ ≡ 0
payload-s₃ = refl
