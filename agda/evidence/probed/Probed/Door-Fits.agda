-- THE DOOR'S PREMISE, INSTANTIATED AT THE ONE SHAPE THAT CAN BE — and
-- the boundary is the finding rather than the row.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT IS PROBEABLE HERE AND WHAT IS NOT.  The statement's conclusion
-- is a CONJUNCTION indexed by the run — one conjunct per arrival the
-- allowance serves, one per chain that arrival reaches — so it is
-- inhabited by constructors rather than decided by a numeral, and a row
-- is a term someone has to write.  `PathFits` has three of them, and
-- only `at-root` asks for nothing: `through` wants the frame shelf,
-- whose obligations are still postulates, and `at-sink` wants a
-- fan-out nothing yet proves.  So the region a postulate-free row can
-- reach is exactly the chains with no frame on them.
--
-- THE FIRST FAMILY IS IN IT AND IS NOT VACUOUS.  A bare slot subscribed
-- at the root registers one chain, that chain is `root`, and the slot's
-- single value arrives after the subscribe frame — so the allowance
-- serves a real arrival and the conjunction it reduces to has a real
-- conjunct in it.  All three figures are pinned separately below,
-- because each is a way this row could have been green having asked for
-- nothing: no arrival at all sends `DrainFits` to `⊤`, an arrival
-- reaching no chain sends `ArrivalFits` to `⊤` as well, and a chain
-- carrying a frame would not have admitted `at-root` in the first
-- place.
--
-- AND THE SECOND FAMILY IS THE BOUNDARY, WHICH IS WHY IT HAS NO FIT
-- ROW.  One flattener over a map of the arriving value builds a chain
-- two frames deep, so its conjunct needs `through` twice and cannot be
-- written out of anything proven.  The frame count is pinned instead:
-- it says where the premise stops being constructible from what this
-- development has, and it is the shape the tier's next leg has to
-- reach.  A fit row there would be a postulate handed back as its own
-- evidence.
--
-- TARGET: entry-drain-fits @81d1bb
module Probed.Door-Fits where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_; length; map)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂;
  ofᵉ; mapᵉ; mergeAllᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠_;
  chainsOf; sched-next; subscribeE; rootWitness; sched-init; st-init)
open import Verify-Rank-Sufficient using (entry-drain-fits)
open import Verify-Rank-Sufficient.Fits using (at-root)
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
-- THE ENTRY, AND IT IS THE STATEMENT'S OWN.  `entry-drain-fits` names
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
-- THE THREE NON-VACUITY MEASURES.  Each is nought on a run where the
-- corresponding quantifier is empty, so a positive pin is what says the
-- conjunct underneath was asked for rather than skipped.
----------------------------------------------------------------------

pathLen : ∀ {s t} → Path Γ₁ s t → ℕ
pathLen root           = 0
pathLen (share-sink _) = 0
pathLen (_ ↠ p)        = suc (pathLen p)

arrived : (e : Closed Γ₁ natᵗ) → ℕ
arrived e with sched-next (entOf e)
... | inj₁ _ = 0
... | inj₂ _ = 1

reached : (e : Closed Γ₁ natᵗ) → ℕ
reached e with sched-next (entOf e)
... | inj₁ _       = 0
... | inj₂ (a , _) = length (chainsOf a (stOf e))

frames : (e : Closed Γ₁ natᵗ) → ℕ
frames e with sched-next (entOf e)
... | inj₁ _       = 0
... | inj₂ (a , _) = sum (map (λ rp → pathLen (proj₂ rp)) (chainsOf a (stOf e)))

----------------------------------------------------------------------
-- THE ROW.  One allowance, one arrival, one chain, no frame on it —
-- and the fit is the conjunction the statement reduces to at exactly
-- that point, written out of constructors and nothing else.
----------------------------------------------------------------------

bareArrived : arrived bare ≡ 1
bareArrived = refl

bareReached : reached bare ≡ 1
bareReached = refl

bareFrames : frames bare ≡ 0
bareFrames = refl

doorBare : Confirms (entry-drain-fits 1 bare insLate)
doorBare = (at-root , tt) , tt

----------------------------------------------------------------------
-- AND THE BOUNDARY, PINNED RATHER THAN CLAIMED.  Same slot, same
-- arrival, a chain two frames deep — so the conjunct here is a
-- `through` over a `through`, and both want the shelf.
----------------------------------------------------------------------

flatArrived : arrived flat ≡ 1
flatArrived = refl

flatReached : reached flat ≡ 1
flatReached = refl

flatFrames : frames flat ≡ 2
flatFrames = refl
