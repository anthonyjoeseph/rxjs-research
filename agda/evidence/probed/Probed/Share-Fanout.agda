----------------------------------------------------------------------
-- WHAT THE SHARE DISPATCH DOES TO THE STORE, which is the one thing
-- the sink's obligation has to be stated against.  A sink ends its own
-- chain and hands its values to every chain registered on the share,
-- and those chains are folded THREADING ONE STATE: the second chain is
-- entered at whatever the first one left.  So a sink clause stating its
-- bound at the store the dispatch was ENTERED at is a different
-- statement from one stating it at what the fan-out reaches, and until
-- the two are told apart nothing says which one the fold can spend.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- THE TWO CANDIDATES, SEPARATED RATHER THAN ARGUED.  Both read the same
-- run; they differ only in where the store is read.  The entry rule
-- reads it before the dispatch, the reached rule after — and a fan-out
-- whose consumers are folds over OBSERVABLES writes a node per chain,
-- so the two come apart at a program this evaluator performs.  A sink
-- clause carrying only the entry figure would therefore be green over a
-- fan-out it had never priced.
----------------------------------------------------------------------


----------------------------------------------------------------------
-- AND THE ROWS SAY THE GROWTH IS NOT IN THE CHAIN COUNT, which is the
-- half a separation cannot buy and the half that decides the shape.
-- The store reading is a MAXIMUM over the machine's nodes, so parallel
-- consumers cannot compound: three consumers at one wrapping rate leave
-- exactly what one consumer at that rate leaves, digit for digit, and a
-- fan-out of three DIFFERENT rates leaves exactly what its deepest
-- consumer alone leaves.  So the residue the sink's clause owes is a
-- join with what a chain's own write reaches, and not a bound that
-- grows with the number of registrations — which is the difference
-- between a clause the chain fold can spend and one it cannot.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- THE QUIET FAN-OUT IS THE CONTROL, and without it the separation
-- above would be a statement about the passage of an instant rather
-- than about the dispatch.  Three consumers of the same share whose
-- accumulators are plain numbers register exactly as widely and leave
-- the store where they found it, so the two rules AGREE there and come
-- apart only where the chains write.  A rule that read the clock rather
-- than the fan-out could not have produced that pair.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- AND THE PAYLOAD READS NOUGHT AT EVERY POINT, which is degenerate as
-- a conjunct and load-bearing as an attribution: the values crossing
-- this share are numbers, so nothing the store gains here was carried
-- in.  Every figure the store rows report is the folds' own re-wrapping
-- of their accumulators.  What is NOT covered is a fan-out whose values
-- are themselves observables, where the two would be summed rather than
-- attributed, and no row here reaches that.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- THE REGISTRATION COUNTS ARE CLAIMED FOR THE OPPOSITE REASON to the
-- store rows: they are what says the fan-out HAPPENED.  A share nothing
-- registered on dispatches to the empty list, leaving every store row
-- below green over a delivery that never ran, and the counts are the
-- only thing separating that reading from this one.
----------------------------------------------------------------------

-- FORK: share-chain-hop
module Probed.Share-Fanout where

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; strmᵗ;
  ofᵉ; scanᵉ; mergeAllᵉ; input; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Hop-Depth using (depthᵉ; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; root; shareAdmit;
  sched-next; cascade; subscribeE; rootWitness; sched-init; st-init;
  arrTy; arrVal; stHop)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Fits using (arrivalRank)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE HARNESS.  Slot zero is a cold script delivering twice after the
-- subscribe frame; slot one is a SHARE over it, so every consumer of
-- slot one is a registration on one source rather than a subscriber of
-- its own.  That is the configuration the cold slot refuses to produce.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

ins : Slots Γ₂
ins zero       = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ []))
ins (suc zero) = shared (input zero)

----------------------------------------------------------------------
-- THE CONSUMERS, at three wrapping rates.  Each is a fold whose
-- accumulator is an OBSERVABLE, so the node its subscribe installs
-- reads positive and the frame's own write deepens it per delivery.
-- The rate is what a chain adds to the store when it is folded.
----------------------------------------------------------------------

deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

deepen2 : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen2 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

deepen3 : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen3 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (strmᵗ (mergeAllᵉ nothing
              (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ []))) ∷ [])))

seed : Tm Γ₂ [] [] [] (obs natᵗ)
seed = strmᵗ (mergeAllᵉ nothing
         (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

cons1 cons2 cons3 : Tm Γ₂ [] [] [] (obs natᵗ)
cons1 = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen  seed (input (suc zero))))
cons2 = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen2 seed (input (suc zero))))
cons3 = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen3 seed (input (suc zero))))

-- and a consumer that FANS OUT WITHOUT WRITING: a fold whose
-- accumulator is a plain number, so the node its subscribe installs
-- reads nought and stays there however many values it is handed
flatCons : Tm Γ₂ [] [] [] (obs natᵗ)
flatCons = strmᵗ (scanᵉ (fstᵗ (varᵗ (here refl))) (nat̂ 0) (input (suc zero)))

-- one consumer, three of the SAME consumer, and three of DIFFERENT
-- rates: the chain count and the rate spread are the two axes
oneProg thriceProg mixedProg quietProg : Closed Γ₂ natᵗ
oneProg    = mergeAllᵉ nothing (ofᵉ (cons3 ∷ []))
thriceProg = mergeAllᵉ nothing (ofᵉ (cons3 ∷ cons3 ∷ cons3 ∷ []))
mixedProg  = mergeAllᵉ nothing (ofᵉ (cons1 ∷ cons2 ∷ cons3 ∷ []))
quietProg  = mergeAllᵉ nothing (ofᵉ (flatCons ∷ flatCons ∷ flatCons ∷ []))

----------------------------------------------------------------------
-- THE INSTRUMENT.  The drain's own step with the emit stream dropped,
-- so every state read below is one the loop itself produced.
----------------------------------------------------------------------

entry : (e : Closed Γ₂ natᵗ) → Sched Γ₂ × EvalSt e
entry e =
  let (_ , sched , st) =
        subscribeE {lo = 2} (rootWitness e ins) e {below-ctx e} root 0 0
          (sched-init e ins) (st-init e)
  in sched , st

stepOnce : {e : Closed Γ₂ natᵗ} → ℕ → Sched Γ₂ × EvalSt e →
  Sched Γ₂ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

stateAt : (e : Closed Γ₂ natᵗ) → ℕ → Sched Γ₂ × EvalSt e
stateAt e zero    = entry e
stateAt e (suc k) = stepOnce (suc k) (stateAt e k)

term : (e : Closed Γ₂ natᵗ) → ℕ
term e = depthᵉ (slotRd ins) e

store : (e : Closed Γ₂ natᵗ) → ℕ → ℕ
store e k with stateAt e k
... | (_ , st) = stHop (slotRd ins) st

rank : (e : Closed Γ₂ natᵗ) → ℕ → ℕ
rank e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _            = 0
...   | inj₂ (a , sched′) = arrivalRank a sched′ st

pay : (e : Closed Γ₂ natᵗ) → ℕ → ℕ
pay e k with stateAt e k
... | (sched , _) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = depthᵛ (slotRd ins) (arrTy a) (arrVal a)

-- how many chains the SHARE itself would fan out to at this point --
-- the count that says a store row priced a delivery rather than an
-- empty list
regs : (e : Closed Γ₂ natᵗ) → ℕ → ℕ
regs e k with stateAt e k
... | (_ , st) = length (shareAdmit (suc zero) (EvalSt.registry st))

----------------------------------------------------------------------
-- THE FORK.  The entry rule reads the store before the dispatch, the
-- reached rule after it; nothing else differs.
----------------------------------------------------------------------

Pt : Set
Pt = Closed Γ₂ natᵗ

entryRule : Pt → ℕ
entryRule e = store e 0

reachedRule : Pt → ℕ
reachedRule e = store e 1

fanoutFork : Separates entryRule reachedRule
fanoutFork = separates-at thriceProg (λ ())

----------------------------------------------------------------------
-- THE ROWS.  Radix 1000, low digit first.
----------------------------------------------------------------------

packOne : ℕ
packOne = regs oneProg 0 + 1000 * (regs oneProg 1
        + 1000 * (store oneProg 0 + 1000 * (store oneProg 1
        + 1000 * (store oneProg 2 + 1000 * (term oneProg
        + 1000 * rank oneProg 0)))))

packThrice : ℕ
packThrice = regs thriceProg 0 + 1000 * (regs thriceProg 1
           + 1000 * (store thriceProg 0 + 1000 * (store thriceProg 1
           + 1000 * (store thriceProg 2 + 1000 * (term thriceProg
           + 1000 * rank thriceProg 0)))))

packMixed : ℕ
packMixed = regs mixedProg 0 + 1000 * (regs mixedProg 1
          + 1000 * (store mixedProg 0 + 1000 * (store mixedProg 1
          + 1000 * (store mixedProg 2 + 1000 * (term mixedProg
          + 1000 * rank mixedProg 0)))))

packPay : ℕ
packPay = pay oneProg 0 + 1000 * (pay oneProg 1
        + 1000 * (pay thriceProg 0 + 1000 * (pay thriceProg 1
        + 1000 * (pay mixedProg 0 + 1000 * pay mixedProg 1))))

oneRow : packOne ≡ 10009007004001001001
oneRow = refl

thriceRow : packThrice ≡ 10009007004001003003
thriceRow = refl

mixedRow : packMixed ≡ 10009007004001003003
mixedRow = refl

payRow : packPay ≡ 0
payRow = refl

-- the agreement, and it is what makes the fork stand for something: a
-- fan-out of the same width whose chains do not WRITE leaves the two
-- rules reading the same figure, so what the fork separates is the
-- dispatch's own write and not the passage of an instant
packQuiet : ℕ
packQuiet = regs quietProg 0 + 1000 * (regs quietProg 1
          + 1000 * (store quietProg 0 + 1000 * (store quietProg 1
          + 1000 * (store quietProg 2 + 1000 * (term quietProg
          + 1000 * rank quietProg 0)))))

quietRow : packQuiet ≡ 1001000000000003003
quietRow = refl

quietAgree : entryRule quietProg ≡ reachedRule quietProg
quietAgree = refl
