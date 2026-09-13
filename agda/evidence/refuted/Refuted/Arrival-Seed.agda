-- THE ARRIVAL'S OWN SEED DOES NOT BOUND THE REGISTRY EITHER, AND IT
-- FAILS BY THE MECHANISM THAT KILLED THE JOIN.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHAT THIS TESTS AND WHY IT WAS THE NEXT THING TO TEST.  Two witnesses
-- already say the registry cannot be fitted against a reading of the
-- TERM, nor against the widest join a STATE admits.  What they left open
-- was the one quantity neither of them is: the rank an ARRIVAL enters
-- at, which the cascade re-seeds per arrival and which is a SUM rather
-- than a join — the term's reading PLUS the payload's joined with the
-- store's.  A sum can exceed every summand, so the arithmetic that
-- killed the join does not obviously kill this, and the seed is what the
-- chain fold actually descends on.  It is therefore the candidate with
-- the best claim to be adequate where the others were not.

-- IT IS NOT, AND THE FIGURES SAY IT FAILS THE SAME WAY.  At the door the
-- seed has room — three against one, four against one — because the
-- payload that is about to arrive reads deep.  One arrival later BOTH
-- variable summands read ZERO: the payload is spent and the store, whose
-- queue held the gate's body, is empty.  The seed collapses onto the
-- term's own reading, which is the quantity the first witness already
-- refuted, while the registry keeps the frame the arrival installed.  So
-- the sum buys nothing at the state where anything is needed.

-- AND THE SECOND PROGRAM SAYS THE GAP IS STILL A RATE.  One more
-- flattener over the same late outer takes the registry to three against
-- the same seed of one, so no fixed slack added to the seed repairs it —
-- which rules out the reading that the seed is merely a constant short.

-- WHAT IS DEAD IS THE MECHANISM, NOT THIS STATEMENT ALONE.  Three
-- successive candidates for what bounds the registry at a drain step —
-- the term, the widest state join, and now the arrival's seed — are each
-- refuted, and none is a sub-case of the one before.  The quantity that
-- has to be adequate is not a bound on the REGISTRY at all: the registry
-- prices what a chain COULD spend given an arbitrarily deep value, while
-- a fold spends what the value it is actually handed makes it spend.
module Refuted.Arrival-Seed where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _+_; _≤_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; obs; strmᵗ; ofᵉ; mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; ε; mapStep; flatten; hopOf; depthᵉ; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; Sched; EvalSt; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner; thru-outer;
  RegRow; arrTy; arrVal; cascade; sched-next; subscribeE; rootWitness; sched-init; st-init; stHop)
open import Rx.Inputs-Below using (below-ctx)

----------------------------------------------------------------------
-- THE CURRENCY, WRITTEN OUT HERE RATHER THAN IMPORTED.  A repair that
-- changed what a chain's frames are priced at must make these rows fail
-- by name rather than quietly agree with them.
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

regsDepth′ : ∀ {n} {Γ : Ctx n} {t} (ψ : Fin n → Rd₃) →
             List (RegRow Γ t) → ℕ
regsDepth′ ψ []                   = 0
regsDepth′ ψ ((rid , src , c) ∷ r) =
  hopOf (chainRd′ ψ (proj₂ c) (0 , 0 , 0)) ⊔ regsDepth′ ψ r

----------------------------------------------------------------------
-- THE SEED, SPELLED AS THE EVALUATOR SPELLS IT.  The addend is the
-- payload's reading joined with the store's, exactly as the arrival's
-- own witness is minted, and the sum with the term's reading is the
-- rank component the chain fold descends on.  Read at the schedule's
-- NEXT arrival, since that is the one the drain is about to serve.
----------------------------------------------------------------------

addend : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
addend sched st with sched-next sched
... | inj₁ _       = stHop (slotRd (Sched.slots sched)) st
... | inj₂ (a , _) =
  depthᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a)
  ⊔ stHop (slotRd (Sched.slots sched)) st

SeedFits′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
            Sched Γ → EvalSt e → Set
SeedFits′ {e = e} sched st =
  let ψ = slotRd (Sched.slots sched) in
  regsDepth′ ψ (EvalSt.registry st) ≤ depthᵉ ψ e + addend sched st

----------------------------------------------------------------------
-- THE STATEMENT.  One arrival, taken through the drain's own step — the
-- same `sched-next` and the same `cascade`, in the same order — so the
-- pair it hands back is the pair the drain would have recursed on,
-- never a state written by hand.
----------------------------------------------------------------------

stepOnce : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Sched Γ × EvalSt e → Sched Γ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

SeedPreserved : Set
SeedPreserved = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nextId : Id) (sched : Sched Γ) (st : EvalSt e) →
  SeedFits′ sched st →
  SeedFits′ (proj₁ (stepOnce {e = e} nextId (sched , st)))
            (proj₂ (stepOnce {e = e} nextId (sched , st)))

----------------------------------------------------------------------
-- THE PROGRAMS, WHICH ARE THE TWO THAT KILLED THE PRESENT PREMISE.  One
-- slot, scripted with values arriving well past the tick a gate's body
-- is scheduled on, so the gate has closed over its flattener by the
-- time anything is delivered.  `q₁` is a flattener whose outer is a
-- gate, behind a second gate; `q₃` is the same with one more flattener
-- over the same late outer.
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
        subscribeE {lo = n} (rootWitness e ins) e {below-ctx e} root 0 0
          (sched-init e ins) (st-init e)
  in sched , st

seed : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Sched Γ × EvalSt e → ℕ
seed e (sched , st) =
  depthᵉ (slotRd (Sched.slots sched)) e + addend sched st

payRd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
payRd (sched , st) with sched-next sched
... | inj₁ _       = 0
... | inj₂ (a , _) = depthᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a)

stRd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
stRd (sched , st) = stHop (slotRd (Sched.slots sched)) st

regRd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
regRd (sched , st) = regsDepth′ (slotRd (Sched.slots sched)) (EvalSt.registry st)

----------------------------------------------------------------------
-- THE CROSSING.  The entry rows are what make this a refutation of
-- PRESERVATION rather than a second witness at the door: the seed has
-- genuine room there — three against a registry of one — and one
-- arrival takes it to one against a registry of two.
----------------------------------------------------------------------

e₁ s₁ : Sched Γ₁ × EvalSt q₁
e₁ = entry q₁ insLate
s₁ = stepOnce 1 e₁

-- LOAD-BEARING: the seed at the door, with room rather than tightly, so
-- the ⊥ below cannot be read as an entry failure the premise inherits
seed-e₁ : seed q₁ e₁ ≡ 3
seed-e₁ = refl

fit-e₁ : SeedFits′ (proj₁ e₁) (proj₂ e₁)
fit-e₁ = s≤s z≤n

-- LOAD-BEARING: one arrival later the seed is the TERM's own reading
-- and nothing more, which is the quantity a sibling witness already
-- refuted — so the sum has bought nothing where it was needed
seed-s₁ : seed q₁ s₁ ≡ 1
seed-s₁ = refl

-- LOAD-BEARING: and it collapsed because BOTH variable summands are
-- zero.  A repair that read either one differently would move these
-- rows; a repair that merely widened the seed would not
pay-s₁ : payRd s₁ ≡ 0
pay-s₁ = refl

seed-store-s₁ : stRd s₁ ≡ 0
seed-store-s₁ = refl

-- LOAD-BEARING: the registry did not merely fail to shrink — it GREW
-- across the same step the seed collapsed on, which is what makes the
-- two sides cross rather than merely meet
reg-e₁ : regRd e₁ ≡ 1
reg-e₁ = refl

reg-s₁ : regRd s₁ ≡ 2
reg-s₁ = refl

seed-preserved-false : SeedPreserved → ⊥
seed-preserved-false h with h 1 (proj₁ e₁) (proj₂ e₁) fit-e₁
... | s≤s ()

----------------------------------------------------------------------
-- AND THE GAP IS A RATE HERE TOO.  One more flattener over the same
-- late outer leaves the seed at one and takes the registry to three, so
-- a fixed slack added to the seed repairs neither program.  These rows
-- are pinned rather than spent: the ⊥ is already had, and what they buy
-- is that it is not an off-by-one.
----------------------------------------------------------------------

e₃ s₃ : Sched Γ₁ × EvalSt q₃
e₃ = entry q₃ insLate
s₃ = stepOnce 1 e₃

-- LOAD-BEARING: the deeper program's door has MORE room, not less, so
-- the collapse below is not the entry being tighter
seed-e₃ : seed q₃ e₃ ≡ 4
seed-e₃ = refl

seed-s₃ : seed q₃ s₃ ≡ 1
seed-s₃ = refl

pay-s₃ : payRd s₃ ≡ 0
pay-s₃ = refl

seed-store-s₃ : stRd s₃ ≡ 0
seed-store-s₃ = refl

-- LOAD-BEARING, AND THIS IS THE RATE: the same one arrival takes this
-- registry to THREE against the same seed of one, so the gap grows with
-- the program rather than sitting a fixed distance away
reg-e₃ : regRd e₃ ≡ 1
reg-e₃ = refl

reg-s₃ : regRd s₃ ≡ 3
reg-s₃ = refl
