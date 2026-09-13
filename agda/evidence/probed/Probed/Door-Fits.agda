-- THE DOOR'S PREMISE, INSTANTIATED — and the region it reaches is the
-- one its predecessor recorded as unreachable.  The statement here used
-- to be a whole fit certificate, so a row could only stand where every
-- constructor it needed was already proven: the chains with no frame on
-- them, and nothing else.  The premise is now a COUNT of flatteners
-- against the program's own reading, which computes at every chain, so
-- the two-frame chain that was pinned as a boundary is a row.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- THE LOAD-BEARING ROW IS THE FLATTENED ONE, AND IT COMES BACK TIGHT.
-- Its chain carries one flattener and the program reads one, so the
-- premise holds with NO MARGIN — a reading that charged the flattener
-- anything more, or a program reading that charged it anything less,
-- crosses here.  That is what says the count and the reading are in the
-- same currency rather than merely both being small.

-- THE BARE ROW IS DEGENERATE IN EVERY COMPONENT AND IS CLAIMED AS A
-- CONTROL RATHER THAN AS COVERAGE.  Its chain is the root, so the
-- count is nought, the payload is a number and reads nought, and the
-- rank it is held under is nought too — the conjunct could not have
-- failed.  What it pins is that the allowance serves an arrival at all
-- and that the arrival reaches a chain, which is how the flattened
-- row's own reduction is known to be asking for something.

-- NOT COVERED.  Every row stands at ONE arrival over ONE cold slot, so
-- nothing here reaches the allowance's second conjunct, a share, or a
-- registry holding more than one chain — and a chain with TWO
-- flatteners, where the reading would have to supply two, is the
-- nearest uncovered shape rather than a different question.
-- TARGET: entry-drain-hop @5b9789
module Probed.Door-Fits where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂;
  ofᵉ; mapᵉ; mergeAllᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (depthᵛ; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; subscribeE;
  rootWitness; sched-init; st-init; sched-next; chainsOf; cascadeLatch;
  arrTy; arrVal; RegId)
open import Verify-Rank-Sufficient using (entry-drain-hop)
open import Verify-Rank-Sufficient.Fits using (arrivalRank)
open import Verify-Rank-Sufficient.Path-Fits using (pathHops)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE SLOT.  One input, cold, nothing in the subscribe frame and a
-- single value one tick out — so the door returns before anything is
-- delivered and the allowance is what serves it.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

bare : Closed Γ₁ natᵗ
bare = input zero

lit : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
lit = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

flat : Closed Γ₁ natᵗ
flat = mergeAllᵉ nothing (mapᵉ lit (input zero))

----------------------------------------------------------------------
-- THE ENTRY, AND IT IS THE STATEMENT'S OWN.  `entry-drain-hop` names
-- the pair `subscribeE` returns at the root; nothing here is written by
-- hand, which is what makes the figures below about a REACHED state.
----------------------------------------------------------------------

entOf : (e : Closed Γ₁ natᵗ) → Sched Γ₁
entOf e = proj₁ (proj₂ (subscribeE (rootWitness e insLate) e root 0 0
            (sched-init e insLate) (st-init e)))

stOf : (e : Closed Γ₁ natᵗ) → EvalSt e
stOf e = proj₂ (proj₂ (subscribeE (rootWitness e insLate) e root 0 0
           (sched-init e insLate) (st-init e)))

----------------------------------------------------------------------
-- THE FIGURES, TAKEN AT THE OBLIGATION'S OWN POINT.  The state is the
-- latched one with this registration marked delivered, which is the
-- state the premise's first conjunct is stated against — so a row that
-- read the entry state instead would be comparing against a rank the
-- statement never mentions.
----------------------------------------------------------------------

atArrival : (e : Closed Γ₁ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ
atArrival e with sched-next (entOf e)
... | inj₁ _        = 0 , 0 , 0 , 0 , 0
... | inj₂ (a , sd) = go (chainsOf a (stOf e))
  where
  lat : EvalSt e
  lat = cascadeLatch a (stOf e)

  go : List (RegId × Path Γ₁ (arrTy a) natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ
  go []               = 0 , 0 , 0 , 0 , 0
  go ((rid , c) ∷ cs) =
    let st′ = record lat { delivered = rid ∷ EvalSt.delivered lat }
        ψ   = slotRd (Sched.slots sd)
    in depthᵛ ψ (arrTy a) (arrVal a) , pathHops c , arrivalRank a sd st′
     , depthᵉ ψ e , suc (length cs)

pay hops rank term reach : (e : Closed Γ₁ natᵗ) → ℕ
pay   e = proj₁ (atArrival e)
hops  e = proj₁ (proj₂ (atArrival e))
rank  e = proj₁ (proj₂ (proj₂ (atArrival e)))
term  e = proj₁ (proj₂ (proj₂ (proj₂ (atArrival e))))
reach e = proj₂ (proj₂ (proj₂ (proj₂ (atArrival e))))

----------------------------------------------------------------------
-- THE ROWS.  Five figures per program, packed so one error reports all
-- of them: payload, flattener count, the rank the chain is held under,
-- the program's own reading, and how many chains the arrival reached.
----------------------------------------------------------------------

packBare packFlat : ℕ
packBare = pay bare + 10 * hops bare + 100 * rank bare
         + 1000 * term bare + 10000 * reach bare
packFlat = pay flat + 10 * hops flat + 100 * rank flat
         + 1000 * term flat + 10000 * reach flat

-- DEGENERATE in all four of its comparing components, and pinned so
-- that the row below cannot be read as covering what this one does not:
-- the arrival is served and reaches one chain, and everything the
-- premise compares there is nought
bareRow : packBare ≡ 10000
bareRow = refl

-- LOAD-BEARING, and TIGHT: the chain's one flattener is paid by the
-- program's reading of one, with the payload contributing nothing, so
-- the premise holds by equality.  A flattener priced at more than one,
-- or a program reading that did not charge for its own, crosses here
flatRow : packFlat ≡ 11110
flatRow = refl

----------------------------------------------------------------------
-- AND THE STATEMENT ITSELF, at both points.  The type is generated by
-- Agda from `entry-drain-hop` as it now reads, so the probe chooses the
-- program and nothing else; a restatement changes what these rows have
-- to inhabit.
----------------------------------------------------------------------

doorBare : Confirms (entry-drain-hop 1 bare insLate)
doorBare = (z≤n , tt) , tt

doorFlat : Confirms (entry-drain-hop 1 flat insLate)
doorFlat = (s≤s z≤n , tt) , tt
