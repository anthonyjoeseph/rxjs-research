-- WHAT DOES THE STORE HALF OF THE ARRIVAL RANK BUY?  The rank is the
-- term's own reading plus a JOIN of the arriving payload against the
-- store, and until these rows nothing anywhere had moved either half
-- off nought — every payload reached was data and every state reached
-- held nothing.  So the rank had only ever been compared at the term's
-- figure alone, and a rule dropping the store from the join would have
-- been green at every point this development had instantiated.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- THE STORE IS MOVED BY RUNNING AND NOT BY INSTALLING, which is what
-- makes these rows different from the shelf's.  A fold whose SEED is
-- itself a live observable installs its node at the subscribe, so the
-- first state the machine produces already reads positive — no node is
-- handed in, and every figure below is off a state the evaluator built.
-- The fork then stands where the two halves disagree: the payload reads
-- nought and the store reads one, so a term-only rule and the rank
-- differ by exactly the store.

-- AND THE FOLD'S FIXED STORE BOUND SURVIVES, FOR A REASON THE FIGURES
-- NAME.  A chain is threaded under ONE store bound taken at its
-- arrival, so a cascade adding more to the store than the rank carries
-- would refute the shape rather than an arm.  Swept at three folds
-- wrapping their accumulator once, twice and three times per delivery:
-- what a cascade ADDS is exactly the wrap, while the term's own reading
-- is twice the wrap and two more — so the margin grows faster than the
-- debt, and the least reading is a whole term ahead at every row.  The
-- rank is re-seeded at each arrival off the store it finds, so the
-- climb across arrivals is paid for rather than accumulated.

-- WHAT WOULD STILL REFUTE IT IS COMPOUNDING ACROSS CHAINS, AND IT IS
-- NOT REACHABLE FROM HERE.  Several chains under one arrival are
-- threaded under that one bound in sequence, so writes that added up
-- would outrun it.  Both slot kinds were run and neither produces the
-- configuration: a cold slot mints a fresh source per subscriber, so
-- three folds over one script are three arrivals rather than one
-- arrival to three chains, measured at one chain per arrival at every
-- step of the drain; and a SHARED slot does fan out, but not through
-- the chain list — the chain its arrival reaches carries one sink and
-- no frame at all, so the whole of the fan-out is inside the share's
-- own dispatch.  The residual risk is therefore not in the chain fold,
-- and the statement carrying it is the sink's.

-- FORK: entry-drain-hop
module Probed.Store-Rank where

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; length; map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; strmᵗ;
  ofᵉ; scanᵉ; mergeAllᵉ; input; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Hop-Depth using (depthᵉ; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠_;
  thru-outer; from-inner; chainsOf; sched-next; cascade; subscribeE;
  rootWitness; sched-init; st-init; arrTy; arrVal; stHop)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Fits using (arrivalRank)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE COLD HARNESS.  One script delivering twice after the subscribe
-- frame, so every arrival below is served by the allowance.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ []))

----------------------------------------------------------------------
-- THE FOLDS, at three wrapping rates.  Each re-wraps its accumulator
-- once, twice or three times per delivery, so what the store gains per
-- cascade is a parameter rather than a fixed figure.
----------------------------------------------------------------------

deepen : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

deepen2 : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen2 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

deepen3 : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen3 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (strmᵗ (mergeAllᵉ nothing
              (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ []))) ∷ [])))

-- the seed is itself a LIVE observable, so the node the subscribe
-- installs reads positive at the first state the machine produces
liveSeed : Tm Γ₁ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

storeProg fastProg fasterProg : Closed Γ₁ natᵗ
storeProg  = mergeAllᵉ nothing (scanᵉ deepen  liveSeed (input zero))
fastProg   = mergeAllᵉ nothing (scanᵉ deepen2 liveSeed (input zero))
fasterProg = mergeAllᵉ nothing (scanᵉ deepen3 liveSeed (input zero))

-- three folds over ONE script, which is the configuration a cold slot
-- refuses to turn into one arrival reaching three chains
manyProg : Closed Γ₁ natᵗ
manyProg = mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (mergeAllᵉ nothing (scanᵉ deepen  liveSeed (input zero)))
       ∷ strmᵗ (mergeAllᵉ nothing (scanᵉ deepen2 liveSeed (input zero)))
       ∷ strmᵗ (mergeAllᵉ nothing (scanᵉ deepen3 liveSeed (input zero))) ∷ []))

----------------------------------------------------------------------
-- THE INSTRUMENT.  The drain's own step with the emit stream dropped,
-- so every state below is one the loop itself produced.
----------------------------------------------------------------------

entry : (e : Closed Γ₁ natᵗ) → Sched Γ₁ × EvalSt e
entry e =
  let (_ , sched , st) =
        subscribeE {lo = 1} (rootWitness e insLate) e root 0 0
          (sched-init e insLate) (st-init e)
  in sched , st

stepOnce : {e : Closed Γ₁ natᵗ} → Id → Sched Γ₁ × EvalSt e →
  Sched Γ₁ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

stateAt : (e : Closed Γ₁ natᵗ) → ℕ → Sched Γ₁ × EvalSt e
stateAt e zero    = entry e
stateAt e (suc k) = stepOnce (suc k) (stateAt e k)

term : (e : Closed Γ₁ natᵗ) → ℕ
term e = depthᵉ (slotRd insLate) e

pay : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
pay e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = depthᵛ (slotRd insLate) (arrTy a) (arrVal a)

store : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
store e k with stateAt e k
... | (_ , st) = stHop (slotRd insLate) st

rank : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
rank e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _            = 0
...   | inj₂ (a , sched′) = arrivalRank a sched′ st

reach : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
reach e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = length (chainsOf a st)

----------------------------------------------------------------------
-- THE TWO CANDIDATE RULES, as two definitions of one signature over
-- the runs below.  One reads the store into the bound a chain is
-- stated against and the other does not; everything else is shared, so
-- a disagreement is the store's alone.
----------------------------------------------------------------------

Pt : Set
Pt = Closed Γ₁ natᵗ × ℕ

-- the store is not part of what a chain may enter, so the bound is the
-- term's own reading and the payload the arrival carries
termOnly : Pt → ℕ
termOnly (e , k) = term e + pay e k

-- the statement's own rank: the term's reading plus the JOIN
withStore : Pt → ℕ
withStore (e , k) = rank e k

----------------------------------------------------------------------
-- AND THE SEPARATION.  At the first arrival of the live-seeded fold
-- the payload reads nought while the fold's own node reads one, so the
-- two rules differ by exactly the store — the first point anywhere
-- that tells the join's two halves apart.
----------------------------------------------------------------------

storeFork : Separates termOnly withStore
storeFork = separates-at (storeProg , 0) (λ ())

----------------------------------------------------------------------
-- THE FIGURES THE FORK STANDS ON.  Packed radix 1000, low digit
-- first.  Each is a way the separation could have been green having
-- compared nothing: a payload that was never nought would leave the
-- join undecided, a store that never moved would make the rank the
-- term's figure again, and an arrival reaching no chain would send
-- both rules past the comparison entirely.
--
-- term, payload, store in, rank, store after one cascade, chains
----------------------------------------------------------------------

packA : (e : Closed Γ₁ natᵗ) → ℕ
packA e = term e
        + 1000 * pay e 0
        + 1000000 * store e 0
        + 1000000000 * rank e 0
        + 1000000000000 * store e 1
        + 1000000000000000 * reach e 0

liveA : packA storeProg ≡ 1002005001000004
liveA = refl

fastA : packA fastProg ≡ 1003007001000006
fastA = refl

----------------------------------------------------------------------
-- THE MARGIN, AT THREE WRAPPING RATES.  What a cascade adds to the
-- store is the wrap; what the term reads is twice the wrap and two
-- more.  The three-wrap fold is pinned beside the other two so the
-- relation is read off three points rather than asserted.
--
-- term, store in, store after one cascade, rank, term, chains
----------------------------------------------------------------------

packC : ℕ
packC = term fasterProg
      + 1000 * store fasterProg 0
      + 1000000 * store fasterProg 1
      + 1000000000 * rank fasterProg 0
      + 1000000000000 * term manyProg
      + 1000000000000000 * reach manyProg 0

fasterC : packC ≡ 1009009004001008
fasterC = refl

----------------------------------------------------------------------
-- AND THE SECOND ARRIVAL, which is what says the climb across arrivals
-- is paid for: the rank is re-seeded off the store it finds, so it
-- rises with it rather than being outrun.
--
-- payload, rank, store, rank, store, chains
----------------------------------------------------------------------

packB : (e : Closed Γ₁ natᵗ) → ℕ
packB e = pay e 1
        + 1000 * rank e 1
        + 1000000 * store e 2
        + 1000000000 * rank e 2
        + 1000000000000 * store e 3
        + 1000000000000000 * reach e 1

liveB : packB storeProg ≡ 1003000003006000
liveB = refl

----------------------------------------------------------------------
-- THE COLD SLOT REFUSES TO FAN OUT, which is the finding rather than a
-- control: three folds over one script reach ONE chain per arrival at
-- every step of the drain, because a cold slot mints a fresh source
-- per subscriber.  So no cold run puts two chains under one store
-- bound, however many folds it carries.
--
-- chains, chains, chains, store, store, store, rank
----------------------------------------------------------------------

packD : ℕ
packD = reach manyProg 0
      + 1000 * reach manyProg 1
      + 1000000 * reach manyProg 2
      + 1000000000 * store manyProg 0
      + 1000000000000 * store manyProg 1
      + 1000000000000000 * store manyProg 2
      + 1000000000000000000 * rank manyProg 0

manyD : packD ≡ 10003002001001001001
manyD = refl

----------------------------------------------------------------------
-- THE SHARED SLOT, which is the only thing in this machine that hands
-- one arrival to several subscribers.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

insShared : Slots Γ₂
insShared zero       = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ []))
insShared (suc zero) = shared (input zero)

sDeepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
sDeepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

sSeed : Tm Γ₂ [] [] [] (obs natᵗ)
sSeed = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

sFold : Tm Γ₂ [] [] [] (obs natᵗ)
sFold = strmᵗ (mergeAllᵉ nothing (scanᵉ sDeepen sSeed (input (suc zero))))

sharedProg : Closed Γ₂ natᵗ
sharedProg = mergeAllᵉ nothing (ofᵉ (sFold ∷ sFold ∷ sFold ∷ []))

sEntry : Sched Γ₂ × EvalSt sharedProg
sEntry =
  let (_ , sched , st) =
        subscribeE {lo = 2} (rootWitness sharedProg insShared) sharedProg
          root 0 0
          (sched-init sharedProg insShared) (st-init sharedProg)
  in sched , st

sStep : Id → Sched Γ₂ × EvalSt sharedProg → Sched Γ₂ × EvalSt sharedProg
sStep nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

sAt : ℕ → Sched Γ₂ × EvalSt sharedProg
sAt zero    = sEntry
sAt (suc k) = sStep (suc k) (sAt k)

sReach : ℕ → ℕ
sReach k with sAt k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = length (chainsOf a st)

sStore : ℕ → ℕ
sStore k with sAt k
... | (_ , st) = stHop (slotRd insShared) st

sRank : ℕ → ℕ
sRank k with sAt k
... | (sched , st) with sched-next sched
...   | inj₁ _            = 0
...   | inj₂ (a , sched′) = arrivalRank a sched′ st

sinks : ∀ {lo s t} → Path Γ₂ lo s t → ℕ
sinks root             = 0
sinks (share-sink _ _) = 1
sinks (_ ↠ p)          = sinks p

souters : ∀ {lo s t} → Path Γ₂ lo s t → ℕ
souters root                 = 0
souters (share-sink _ _)     = 0
souters (thru-outer _ _ ↠ p) = suc (souters p)
souters (_ ↠ p)              = souters p

sinners : ∀ {lo s t} → Path Γ₂ lo s t → ℕ
sinners root                   = 0
sinners (share-sink _ _)       = 0
sinners (from-inner _ _ _ ↠ p) = suc (sinners p)
sinners (_ ↠ p)                = sinners p

sOver : (∀ {lo s t} → Path Γ₂ lo s t → ℕ) → ℕ → ℕ
sOver f k with sAt k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = sum (map (λ rp → f (proj₂ (proj₂ rp))) (chainsOf a st))

----------------------------------------------------------------------
-- AND THE SHARED ARRIVAL REACHES ONE CHAIN TOO, carrying one sink and
-- NO frame — so the three folds are reached through the share's own
-- dispatch and not through the chain list.  That is what puts the
-- compounding risk in the sink's obligation rather than in this one.
--
-- term, chains, chains, store, store, store, rank
----------------------------------------------------------------------

packE : ℕ
packE = depthᵉ (slotRd insShared) sharedProg
      + 1000 * sReach 0
      + 1000000 * sReach 1
      + 1000000000 * sStore 0
      + 1000000000000 * sStore 1
      + 1000000000000000 * sStore 2
      + 1000000000000000000 * sRank 0

sharedE : packE ≡ 6003002001001001005
sharedE = refl

----------------------------------------------------------------------
-- THE CHAIN'S OWN SHAPE, which is what the sentence above rests on: a
-- sink and nothing else.  The two frame counts are pinned for the
-- opposite reason to the sink — they are nought, and that is the
-- finding.
--
-- sinks, outer frames, exit frames, chains, chains, store, rank
----------------------------------------------------------------------

packF : ℕ
packF = sOver sinks 0
      + 1000 * sOver souters 0
      + 1000000 * sOver sinners 0
      + 1000000000 * sReach 2
      + 1000000000000 * sReach 3
      + 1000000000000000 * sStore 3
      + 1000000000000000000 * sRank 1

sharedF : packF ≡ 7003000000000000001
sharedF = refl
