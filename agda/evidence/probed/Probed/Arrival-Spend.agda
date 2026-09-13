-- THE ARRIVAL READS ITS OWN VALUE, AND THAT IS THE QUANTITY.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHAT IS BEING CHOSEN BETWEEN.  An arrival's cascade enters the chain
-- fold at a rank, and the rank descends once per inner subscription, so
-- a rank that starts too low emits the dry marker the tier's statement
-- says never appears.  Two rules for that rank are on the table.  One
-- reads nothing off the run: the term's own reading is the whole rank,
-- which is what every candidate refuted so far was trying to make
-- sufficient by bounding some part of the state against it.  The other
-- adds a quantity read at the arrival itself.  The rows decide between
-- them, and what they decide is not close.

-- THE PROGRAM THAT SEPARATES THEM, and it is the shape the campaign had
-- already isolated rather than a new one.  A ladder four flattenings
-- deep sits behind a gate, and the reading cuts a gate to a constant
-- deliberately, so that unfolding cannot move it.  The term therefore
-- reads ONE while the body it will deliver is worth FOUR.  At the second
-- arrival the first rule goes dry and the second does not.

-- AND THE MARGIN IS NIL, WHICH IS WHAT MAKES IT WORTH HAVING.  The rank
-- is swept by hand from nought to five at that arrival: it is dry at
-- every one of nought through four and green at five.  The evaluator
-- supplies one plus four at the same point.  So the rule in the code is
-- not merely sufficient here, it is EXACT — a unit less and the run goes
-- dry — and no slack is hiding a quantity that has not been paid for.

-- WHICH QUANTITY, AND IT IS NOT ANY OF THE THREE.  The four comes from
-- reading the arriving VALUE, not the registry, not the store and not a
-- maximum over the schedule.  A value delivered off the schedule carries
-- its own depth, because it is a value rather than a name for one, so
-- the frame meeting it has the figure in its hand and needs nothing
-- carried to it.  That is why every candidate bounding some part of the
-- STATE against the term was refuted: they were all bounding the wrong
-- thing, and the quantity they were trying to reach is one the code
-- already computes at the only place it is wanted.

-- WHAT THE OTHER TWO PROGRAMS ADD, and they are the reason to believe
-- the separation is about depth.  The pair that killed all three
-- registry candidates is run here too, and both rules agree at all six
-- of their arrivals: the addend the evaluator supplies is two and three
-- at their doors and nought after, and the term's own reading carries
-- every one of them.  So the addend is slack exactly where the payload
-- is shallow and exact where it is deep, which is the behaviour a
-- payload reading has and a state maximum does not.

-- THE BOUNDARY.  Three programs, one slot, one flattening strategy;
-- three arrivals each and no burst delivering many times inside one
-- cascade.  The deep arm is deep in the GATED direction only — a ladder
-- behind one gate — and nothing here reaches a gate behind a gate, where
-- two constants would have to compose.  The sweep is over the rank and
-- not over the store, which is nought at every point reached: what a
-- deep store does to the same comparison is untouched.

-- FORK: entry-drain-hop
module Probed.Arrival-Spend where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _+_; _*_; _∸_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Probed.Apparatus using (Separates; separates-at)

open import Rx.Prim using (Id; cold; after_,_; exhausted; close)
open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; obs; strmᵗ; ofᵉ;
  mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (depthᵉ; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (AtFloor; RegId; Sched; EvalSt; Stream; Arrival;
  root; subscribeE; rootWitness; sched-init; st-init; sched-next; cascade;
  cascadeLatch; chainsOf; foldPath; entryWitness; stHop; hasDry;
  arrTick; arrSource; arrTy; arrVal)
open import Rx.Inputs-Below using (below-ctx)

----------------------------------------------------------------------
-- THE HARNESS, recovered from `Refuted.Fit-Cascade` — the two programs
-- at which all three registry candidates crossed.
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

-- THE DEEP BODY, which is the shape the leg is actually about: a ladder
-- behind a gate, so the arrival carries a value worth four while the
-- reading of the term that scheduled it is a constant.
d1 d2 d3 d4 : ∀ {Δᵍ Δ} → Exp Γ₁ Δᵍ Δ [] (obs natᵗ)
d1 = ofᵉ (strmᵗ (mergeAllᵉ nothing obsSlot) ∷ [])
d2 = ofᵉ (strmᵗ (mergeAllᵉ nothing d1) ∷ [])
d3 = ofᵉ (strmᵗ (mergeAllᵉ nothing d2) ∷ [])
d4 = ofᵉ (strmᵗ (mergeAllᵉ nothing d3) ∷ [])

qDeep : Closed Γ₁ natᵗ
qDeep = deferᵉ (mergeAllᵉ nothing (deferᵉ d4))

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Sched Γ × EvalSt e
entry {n = n} e ins =
  let (_ , sched , st) =
        subscribeE {lo = n} (rootWitness e ins) e {below-ctx e} root 0 0
          (sched-init e ins) (st-init e)
  in sched , st

stepOnce : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Sched Γ × EvalSt e → Sched Γ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

----------------------------------------------------------------------
-- THE INSTRUMENT.  The cascade's own fold, with the rank ADDEND chosen
-- rather than read off the state: `entryWitness e sl m` stands at
-- `depthᵉ e + m`, so m is exactly the quantity the evaluator supplies
-- as `payload ⊔ store` and the question is the least m that is enough.
----------------------------------------------------------------------

-- the rank's TERM is a parameter too, not only its addend: `foldPath`
-- accepts an accessibility at any triple, so the control below can stand
-- the same cascade at a rank the program's own reading does not supply
foldAllWith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {t′} →
  Closed Γ t′ → ℕ → (a : Arrival Γ) → Id →
  List (RegId × AtFloor Γ (arrTy a) t) → Sched Γ → EvalSt e → Stream Γ t
foldAllWith rk m a id []                  sched st = []
foldAllWith {n = n} rk m a id ((_ , lo , c) ∷ cs) sched st =
  let (emits , sched₁ , st₁) =
        foldPath (entryWitness rk (Sched.slots sched) m)
                 (<-wellFounded-fast (n ∸ lo))
                 id (arrTick a) (arrSource a) c (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ []
                  else [])
                 (Arrival.isLast a) sched st
  in emits ++ foldAllWith rk m a id cs sched₁ st₁

foldAllAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  ℕ → (a : Arrival Γ) → Id → List (RegId × AtFloor Γ (arrTy a) t) →
  Sched Γ → EvalSt e → Stream Γ t
foldAllAt {e = e} m = foldAllWith e m

-- the next arrival's cascade, at a chosen addend
dryAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  ℕ → Id → Sched Γ × EvalSt e → Bool
dryAt m id (sched , st) with sched-next sched
... | inj₁ _            = false
... | inj₂ (a , sched′) =
  hasDry (foldAllAt m a id (chainsOf a st) sched′ (cascadeLatch a st))

-- the same cascade, at a rank chosen by hand
dryWith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {t′} →
  Closed Γ t′ → ℕ → Id → Sched Γ × EvalSt e → Bool
dryWith rk m id (sched , st) with sched-next sched
... | inj₁ _            = false
... | inj₂ (a , sched′) =
  hasDry (foldAllWith rk m a id (chainsOf a st) sched′ (cascadeLatch a st))

-- a term reading nought, so `entryTri` puts the rank at exactly m
flat : Closed Γ₁ natᵗ
flat = input zero

-- and what the evaluator itself supplies there
seedAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
seedAt (sched , st) with sched-next sched
... | inj₁ _            = 0
... | inj₂ (a , sched′) =
  depthᵛ (slotRd (Sched.slots sched′)) (arrTy a) (arrVal a)
  ⊔ stHop (slotRd (Sched.slots sched′)) st

termOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Sched Γ × EvalSt e → ℕ
termOf e (sched , _) = depthᵉ (slotRd (Sched.slots sched)) e

----------------------------------------------------------------------
-- THE ROWS.
----------------------------------------------------------------------

e₁ s₁ s₁₂ : Sched Γ₁ × EvalSt q₁
e₁  = entry q₁ insLate
s₁  = stepOnce 1 e₁
s₁₂ = stepOnce 2 s₁

e₃ s₃ s₃₂ : Sched Γ₁ × EvalSt q₃
e₃  = entry q₃ insLate
s₃  = stepOnce 1 e₃
s₃₂ = stepOnce 2 s₃

packed₁ : ℕ
packed₁ = termOf q₁ e₁
        + 10 * seedAt e₁
        + 100 * seedAt s₁
        + 1000 * seedAt s₁₂
        + 10000 * termOf q₃ e₃
        + 100000 * seedAt e₃
        + 1000000 * seedAt s₃
        + 10000000 * seedAt s₃₂

packed₁-is : packed₁ ≡ 310021
packed₁-is = refl

-- is there an arrival at all, and does its cascade go dry at addend m?
b : Bool → ℕ
b false = 0
b true  = 1

hasNext : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → Bool
hasNext (sched , _) with sched-next sched
... | inj₁ _ = false
... | inj₂ _ = true

packed₂ : ℕ
packed₂ = b (hasNext e₁)
        + 10 * b (hasNext s₁)
        + 100 * b (hasNext s₁₂)

packed₂-is : packed₂ ≡ 111
packed₂-is = refl

-- the decisive sweep: does the arrival's cascade go dry when the rank
-- carries NO addend at all?  low digit first, radix 10
packed₃ : ℕ
packed₃ = b (dryAt 0 9 e₁)
        + 10 * b (dryAt 0 9 s₁)
        + 100 * b (dryAt 0 9 s₁₂)
        + 1000 * b (dryAt 0 9 e₃)
        + 10000 * b (dryAt 0 9 s₃)
        + 100000 * b (dryAt 0 9 s₃₂)

packed₃-is : packed₃ ≡ 0
packed₃-is = refl

-- THE CONTROL.  Every row above is green, so the instrument must be
-- shown able to report the other answer: the same cascades at a rank
-- the program's reading does not supply.  `flat` reads nought, so the
-- middle of the triple is exactly the addend.
flat-reads : depthᵉ (slotRd insLate) flat ≡ 0
flat-reads = refl

packed₄ : ℕ
packed₄ = b (dryWith flat 0 9 e₁)
        + 10 * b (dryWith flat 0 9 s₁)
        + 100 * b (dryWith flat 0 9 s₁₂)
        + 1000 * b (dryWith flat 0 9 e₃)
        + 10000 * b (dryWith flat 0 9 s₃)
        + 100000 * b (dryWith flat 0 9 s₃₂)

packed₄-is : packed₄ ≡ 11011
packed₄-is = refl

-- and one step up, where the middle of the triple equals what the
-- program's own reading already supplies
packed₅ : ℕ
packed₅ = b (dryWith flat 1 9 e₁)
        + 10 * b (dryWith flat 1 9 s₁)
        + 100 * b (dryWith flat 1 9 s₁₂)
        + 1000 * b (dryWith flat 1 9 e₃)
        + 10000 * b (dryWith flat 1 9 s₃)
        + 100000 * b (dryWith flat 1 9 s₃₂)

packed₅-is : packed₅ ≡ 0
packed₅-is = refl

----------------------------------------------------------------------
-- THE DEEP ARM: a payload deeper than the term that scheduled it.
----------------------------------------------------------------------

eD sD sD₂ : Sched Γ₁ × EvalSt qDeep
eD  = entry qDeep insLate
sD  = stepOnce 1 eD
sD₂ = stepOnce 2 sD

-- low digit first, radix 10: the term's own reading, the seed the
-- evaluator supplies at each of the three doors, and whether each has
-- an arrival at all
packed₆ : ℕ
packed₆ = termOf qDeep eD
        + 10 * seedAt eD
        + 100 * seedAt sD
        + 1000 * seedAt sD₂
        + 10000 * b (hasNext eD)
        + 100000 * b (hasNext sD)
        + 1000000 * b (hasNext sD₂)

packed₆-is : packed₆ ≡ 1110421
packed₆-is = refl

-- THE DECIDING SWEEP.  The second arrival is handed a value the
-- evaluator reads at four while the term that scheduled it reads one.
-- So: what is the least rank that carries it?  Six digits, low first,
-- rank nought through five.
packed₇ : ℕ
packed₇ = b (dryWith flat 0 9 sD)
        + 10 * b (dryWith flat 1 9 sD)
        + 100 * b (dryWith flat 2 9 sD)
        + 1000 * b (dryWith flat 3 9 sD)
        + 10000 * b (dryWith flat 4 9 sD)
        + 100000 * b (dryWith flat 5 9 sD)

packed₇-is : packed₇ ≡ 11111
packed₇-is = refl

-- and the other two doors of the same run, at the rank the term alone
-- supplies
packed₈ : ℕ
packed₈ = b (dryAt 0 9 eD)
        + 10 * b (dryAt 0 9 sD)
        + 100 * b (dryAt 0 9 sD₂)

packed₈-is : packed₈ ≡ 10
packed₈-is = refl

----------------------------------------------------------------------
-- THE SEPARATION, in a type.  Two candidate rules for the rank an
-- arrival's cascade enters at, as two definitions of one signature over
-- the states of this run.  They agree at the door and at the third
-- arrival and disagree at the second, which is the one carrying a value
-- the term that scheduled it was charged a constant for.
----------------------------------------------------------------------

-- the term's own reading, with no quantity read off the run at all
byTerm : Sched Γ₁ × EvalSt qDeep → Bool
byTerm s = dryAt 0 9 s

-- the term's reading plus the arrival's own, which is what the
-- evaluator supplies
byArrival : Sched Γ₁ × EvalSt qDeep → Bool
byArrival s = dryAt (seedAt s) 9 s

deepFork : Separates byTerm byArrival
deepFork = separates-at sD (λ ())
