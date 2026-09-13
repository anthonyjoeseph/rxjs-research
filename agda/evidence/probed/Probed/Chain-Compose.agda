-- WHAT DOES AN EXIT FRAME COST?  Every chain a flattener registers is
-- built out of `from-inner` and never out of `thru-outer` — the outer's
-- frame is CONSUMED when its value is subscribed, and the inner is
-- registered under an exit frame instead.  So the arm the shelf prices
-- appears on no chain at all, and the arm every chain is made of is the
-- one arm nothing in the rank development states anything about.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHICH LEAVES TWO CANDIDATE RULES, AND THEY ARE NOT COSMETIC.  Either
-- an exit frame threads the bound it was handed unchanged, or it costs
-- one as a flattener's own frame does.  `innerReact` hands its payload
-- back untouched on every branch but one, which argues for the first;
-- the second is what the frame's position on the chain would suggest,
-- since it is exactly where the descent into the inner was paid for.
-- The fork below is that choice, and the separation says the two rules
-- disagree on a run this evaluator performs — so one of them refutes
-- the tier and the other does not, and the question cannot be left open
-- as a matter of taste.
--
-- WHERE THEY COME APART, AND WHY IT IS A GATE.  Ungated, the two agree
-- at every depth measured, because a stack of k flatteners reads k and
-- registers k exit frames — the figures track exactly.  A gate reads
-- its own frame and NOT its body, so its figure is a constant however
-- deep the body is, while the chain the body registers is as deep as
-- the body.  That is the one place the rules can differ, and the fork
-- stands there.
--
-- NOT COVERED, and both gaps are the store side.  Every payload here
-- reads nought and every state reads nought, so the rank is the term's
-- figure alone and neither the value half nor the store half of
-- `arrivalRank` is separated by anything below.  A run whose values are
-- themselves observables would move both, and no row here is one.
--
-- FORK: entry-drain-hop
module Probed.Chain-Compose where

open import Data.Bool using (Bool)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_; length; map)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; obs; strmᵗ; ofᵉ;
  mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (depthᵉ; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠_;
  thru-outer; from-inner; chainsOf; sched-next; cascade; subscribeE; rootWitness;
  sched-init; st-init; arrTy; arrVal; stHop)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Fits using (arrivalRank)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE HARNESS.  One slot delivering one value after the subscribe
-- frame, so every arrival below is served by the allowance rather than
-- by the door.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

obsSlot : ∀ {Δᵍ Δ} → Exp Γ₁ Δᵍ Δ [] (obs natᵗ)
obsSlot = ofᵉ (strmᵗ (input zero) ∷ [])

-- k flatteners stacked over the slot, each of which registers one
-- `thru-outer` on the chain the arrival reaches
stack₁ stack₂ stack₃ : Closed Γ₁ natᵗ
stack₁ = mergeAllᵉ nothing obsSlot
stack₂ = mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing obsSlot) ∷ []))
stack₃ = mergeAllᵉ nothing
           (ofᵉ (strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (mergeAllᵉ nothing obsSlot) ∷ []))) ∷ []))

-- AND THE SAME STACKS BEHIND A GATE, which is the region the reading
-- treats differently: a door reads its own frame and NOT its body, so
-- the term's figure is a constant however deep the body is, while the
-- chain the body registers is as deep as the body.
gate₁ gate₂ gate₃ : Closed Γ₁ natᵗ
gate₁ = deferᵉ stack₁
gate₂ = deferᵉ stack₂
gate₃ = deferᵉ stack₃

-- AND A CAPPED FLATTENER, which is the only shape that puts anything in
-- a node's QUEUE: at no limit the drain has nothing to drain, so an
-- exit frame is an identity on its payload and the region below it is
-- never entered.
cap₂ : Closed Γ₁ natᵗ
cap₂ = mergeAllᵉ (just 1)
         (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input zero)
             ∷ strmᵗ (input zero) ∷ []))

----------------------------------------------------------------------
-- THE INSTRUMENT.  The drain's own step with the emit stream dropped,
-- so every state below is one the loop itself produced.
----------------------------------------------------------------------

entry : (e : Closed Γ₁ natᵗ) → Sched Γ₁ × EvalSt e
entry e =
  let (_ , sched , st) =
        subscribeE {lo = 1} (rootWitness e insLate) e {below-ctx e} root 0 0
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

----------------------------------------------------------------------
-- THE CHAIN, BY CONSTRUCTOR.  Which arm a chain carries is the whole
-- question, because the shelf says a different thing about each and
-- says nothing at all about one of them.
----------------------------------------------------------------------

outers : ∀ {lo s t} → Path Γ₁ lo s t → ℕ
outers root                 = 0
outers (share-sink _ _)     = 0
outers (thru-outer _ _ ↠ p) = suc (outers p)
outers (_ ↠ p)              = outers p

inners : ∀ {lo s t} → Path Γ₁ lo s t → ℕ
inners root                   = 0
inners (share-sink _ _)       = 0
inners (from-inner _ _ _ ↠ p) = suc (inners p)
inners (_ ↠ p)                = inners p

total : ∀ {lo s t} → Path Γ₁ lo s t → ℕ
total root             = 0
total (share-sink _ _) = 0
total (_ ↠ p)        = suc (total p)

----------------------------------------------------------------------
-- THE THREE READINGS AT ONE ARRIVAL, and the composed demand they have
-- to satisfy.  `rank` is the statement's own `arrivalRank`, so the
-- comparison is against the quantity every obligation of that arrival
-- is actually stated against.
----------------------------------------------------------------------

term : (e : Closed Γ₁ natᵗ) → ℕ
term e = depthᵉ (slotRd insLate) e

rank : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
rank e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _            = 0
...   | inj₂ (a , sched′) = arrivalRank a sched′ st

pay : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
pay e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = depthᵛ (slotRd insLate) (arrTy a) (arrVal a)

store : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
store e k with stateAt e k
... | (_ , st) = stHop (slotRd insLate) st

reach : (e : Closed Γ₁ natᵗ) → ℕ → ℕ
reach e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = length (chainsOf a st)

over : ((∀ {lo s t} → Path Γ₁ lo s t → ℕ)) → (e : Closed Γ₁ natᵗ) → ℕ → ℕ
over f e k with stateAt e k
... | (sched , st) with sched-next sched
...   | inj₁ _       = 0
...   | inj₂ (a , _) = sum (map (λ rp → f (proj₂ (proj₂ rp))) (chainsOf a st))

----------------------------------------------------------------------
-- THE TWO CANDIDATE RULES, as two definitions of one signature over
-- the runs below.  Each says whether every chain the arrival reaches
-- admits the threading; they differ only in what an exit frame costs.
----------------------------------------------------------------------

Pt : Set
Pt = Closed Γ₁ natᵗ × ℕ

-- an exit frame threads what it was handed, so a chain demands only
-- what its payload reads
freeRule : Pt → Bool
freeRule (e , k) = pay e k ≤ᵇ rank e k

-- an exit frame costs one, as a flattener's own frame does
chargedRule : Pt → Bool
chargedRule (e , k) = (pay e k + over total e k) ≤ᵇ rank e k

----------------------------------------------------------------------
-- WHERE THE RULES AGREE, which is what says the separation below is
-- about the gate and not about two rules that differ everywhere.  The
-- ungated stack reads its own depth and registers exactly that many
-- exit frames, so both rules are satisfied at every depth measured;
-- the capped flattener agrees too, at every step of its own drain.
----------------------------------------------------------------------

agree₁ : freeRule (stack₁ , 0) ≡ chargedRule (stack₁ , 0)
agree₁ = refl

agree₂ : freeRule (stack₂ , 0) ≡ chargedRule (stack₂ , 0)
agree₂ = refl

agree₃ : freeRule (stack₃ , 0) ≡ chargedRule (stack₃ , 0)
agree₃ = refl

agreeCap : freeRule (cap₂ , 1) ≡ chargedRule (cap₂ , 1)
agreeCap = refl

----------------------------------------------------------------------
-- AND THE SEPARATION.  At a gate over one flattener the chain carries
-- two exit frames against a rank of one, so the free rule admits the
-- run and the charged rule refuses it.  Whichever is right, the tier
-- cannot be settled without choosing.
----------------------------------------------------------------------

exitFork : Separates freeRule chargedRule
exitFork = separates-at (gate₁ , 1) (λ ())

----------------------------------------------------------------------
-- THE FIGURES THE FORK STANDS ON.  Each is a way the separation could
-- have been green having compared nothing: an arrival reaching no chain
-- sends both rules to the empty quantifier, a chain carrying no frame
-- collapses the charged rule onto the free one, and a rank of nought
-- would refuse every run alike.  The `thru-outer` count is pinned for
-- the opposite reason — it is nought at every point, which is the
-- finding rather than a control.
----------------------------------------------------------------------

-- the ungated stack: the reading and the chain track exactly
uTerm : term stack₃ ≡ 3
uTerm = refl

uReach : reach stack₃ 0 ≡ 1
uReach = refl

uInners : over inners stack₃ 0 ≡ 3
uInners = refl

uOuters : over outers stack₃ 0 ≡ 0
uOuters = refl

uRank : rank stack₃ 0 ≡ 3
uRank = refl

-- the gated stack: the reading is a constant, the chain is not
gTerm : term gate₁ ≡ 1
gTerm = refl

gReach : reach gate₁ 1 ≡ 1
gReach = refl

gInners : over inners gate₁ 1 ≡ 2
gInners = refl

gOuters : over outers gate₁ 1 ≡ 0
gOuters = refl

gRank : rank gate₁ 1 ≡ 1
gRank = refl

-- and the capped flattener, whose queue is the only thing that makes an
-- exit frame do more than relay: still one exit frame, still no outer
capReach : reach cap₂ 1 ≡ 1
capReach = refl

capInners : over inners cap₂ 1 ≡ 1
capInners = refl

capOuters : over outers cap₂ 1 ≡ 0
capOuters = refl

-- AND THE STORE, NOUGHT AT BOTH ENDS OF THE SWEEP.  This is the gap
-- rather than a control: the rank is a sum of the term's figure and a
-- join of the payload against the store, so with both halves of that
-- join at nought every row above compares against the term's figure
-- alone and nothing here separates the other two.
uStore : store stack₃ 0 ≡ 0
uStore = refl

gStore : store gate₁ 1 ≡ 0
gStore = refl
