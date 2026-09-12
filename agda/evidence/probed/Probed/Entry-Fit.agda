-- THE SHAPE THAT ONCE REFUTED THE FIT, NOW CONFIRMING IT — AND THE
-- SEPARATE AXIS THAT SAYS WHY THE ROWS ARE NOT CIRCULAR.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT MAKES A SCRIPTED SLOT THE ADVERSARIAL CASE.  A slot's reading
-- has three components and the syntax forces two of them to zero: a
-- scripted payload satisfies `isData`, so no emission of its can hold
-- an observable.  The count is therefore the only component left to get
-- wrong, and it is the one that reaches the hop — through the
-- flattener's product and then through a fold, which reads the product
-- as HOW MANY TIMES IT REFOLDS.  A slot whose values all arrive after
-- the subscribe frame is where a count taken at that frame reads zero
-- and the whole chain above it collapses with it.
--
-- SO THE ROWS ARE TAKEN AT EXACTLY THAT SLOT.  One input, cold, an
-- EMPTY synchronous part and a single late value; the program flattens
-- a map of the arriving value into a literal and folds over the result.
-- Every layer the registry holds was put there by the chain the root
-- built rather than inherited from a burst, which is what makes the
-- comparison a statement about the door.
--
-- AND THE SECOND FAMILY IS WHAT KEEPS THIS FROM BEING CIRCULAR.  A
-- reading that counts a source's deliveries cannot be checked only
-- against programs whose deliveries are counted: the fold over a
-- RECURSION delivers as many times as the drain lets it, which is not a
-- quantity the term carries at all.  Those rows take the fit at states
-- the loop's own step produced, across six cascades, at the one program
-- whose output is known to outgrow every reading of itself.
--
-- THE BOUNDARY: ONE SLOT, AND NO HOT ONE.  A hot source is anchored at
-- tick zero rather than at the subscription, so its count is an upper
-- bound rather than an exact one; nothing here instantiates that
-- clause, and a row that did would be checking a weaker statement than
-- these are.  The delivery counts are small because each row re-walks
-- the whole subscribe; what is established is that the collapse is
-- gone, not a rate.
--
-- TARGET: entry-hop-fits @9f8beb
module Probed.Entry-Fit where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Fin using (Fin; zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ;
  strmᵗ; nat̂; fstᵗ; varᵗ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; cascade; sched-next; subscribeE;
  rootWitness; root; sched-init; st-init)
open import Verify-Rank-Sufficient using (entry-hop-fits)
open import Verify-Rank-Sufficient.Hop using (regsDepth)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE LATE SLOT.  `cold [] (after 0 , 9 ∷ [])` is the whole point: the
-- subscribe frame hands out nothing, so a count taken at the frame
-- reads zero while the source is scheduled to deliver one.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

step : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

burst6 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst6 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))

casc6 : Closed Γ₁ (obs natᵗ)
casc6 = scanᵉ step (strmᵗ emptyᵉ) (mergeAllᵉ nothing (mapᵉ burst6 (input zero)))

ent₆ : Sched Γ₁ × EvalSt casc6
ent₆ =
  let r = subscribeE (rootWitness casc6 insLate) casc6 root 0 0
            (sched-init casc6 insLate) (st-init casc6)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

ψ₆ : Fin 1 → Rd₃
ψ₆ = slotRd (Sched.slots (proj₁ ent₆))

----------------------------------------------------------------------
-- BOTH SIDES PINNED SEPARATELY, so the row below is not merely green
-- but green with a MARGIN someone can read.  Either figure moving makes
-- this file go red at the pin rather than quietly agreeing.
--
-- These are LOAD-BEARING in the direction that matters: the term side
-- is what a count taken at the subscribe frame would have read as ONE,
-- against a registry of two.
----------------------------------------------------------------------

regs₆ : regsDepth ψ₆ (EvalSt.registry (proj₂ ent₆)) ≡ 2
regs₆ = refl

term₆ : depthᵉ ψ₆ casc6 ≡ 7
term₆ = refl

fitLate : Confirms (entry-hop-fits casc6 insLate)
fitLate = Below

----------------------------------------------------------------------
-- AND THE SAME AT TWENTY-FOUR DELIVERIES UNDER ONE ARRIVAL, which is
-- the axis the term side was blind to: the registry does not move and
-- the term side climbs with the literal, so the margin widens rather
-- than closing.
----------------------------------------------------------------------

burst24 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst24 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ nat̂ 7
  ∷ nat̂ 8 ∷ nat̂ 9 ∷ nat̂ 10 ∷ nat̂ 11 ∷ nat̂ 12 ∷ nat̂ 13 ∷ nat̂ 14 ∷ nat̂ 15
  ∷ nat̂ 16 ∷ nat̂ 17 ∷ nat̂ 18 ∷ nat̂ 19 ∷ nat̂ 20 ∷ nat̂ 21 ∷ nat̂ 22 ∷ nat̂ 23
  ∷ nat̂ 24 ∷ []))

casc24 : Closed Γ₁ (obs natᵗ)
casc24 = scanᵉ step (strmᵗ emptyᵉ)
  (mergeAllᵉ nothing (mapᵉ burst24 (input zero)))

fit24 : Confirms (entry-hop-fits casc24 insLate)
fit24 = Below

----------------------------------------------------------------------
-- THE AXIS THE TERM DOES NOT CARRY.  The source is a recursion, so how
-- many arrivals happen is the DRAIN's business; `stepOnce` is the
-- loop's own step with the emit stream dropped, so each row reads the
-- pair the recursion would have been handed.  This is the program whose
-- output is known to outgrow every reading of itself, which is why the
-- fit surviving it is worth more than the literal rows above.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

stepG : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepG = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

recur : Closed Γ₀ natᵗ
recur = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

fold : Closed Γ₀ (obs natᵗ)
fold = scanᵉ stepG (strmᵗ emptyᵉ) recur

entryG : Sched Γ₀ × EvalSt fold
entryG =
  let r = subscribeE (rootWitness fold ins₀) fold root 0 0
            (sched-init fold ins₀) (st-init fold)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

stepOnce : Id → Sched Γ₀ × EvalSt fold → Sched Γ₀ × EvalSt fold
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

stepN : ℕ → Id → Sched Γ₀ × EvalSt fold → Sched Γ₀ × EvalSt fold
stepN 0       _      p = p
stepN (suc k) nextId p = stepN k (suc nextId) (stepOnce nextId p)

at : ℕ → Sched Γ₀ × EvalSt fold
at k = stepN k 1 entryG

fitsAt : ℕ → Bool
fitsAt k =
  let sched = proj₁ (at k) in
  regsDepth (slotRd (Sched.slots sched)) (EvalSt.registry (proj₂ (at k)))
    ≤ᵇ depthᵉ (slotRd (Sched.slots sched)) fold

-- SIX CASCADES, AND EACH COULD HAVE FAILED: a reading that collapsed at
-- any arrival leaves its conjunct `false` and this row unprovable
survives : (fitsAt 0 ∧ fitsAt 1 ∧ fitsAt 2 ∧ fitsAt 3 ∧ fitsAt 4
            ∧ fitsAt 5) ≡ true
survives = refl

-- and the door of that same program is the target's own statement
fitFold : Confirms (entry-hop-fits fold ins₀)
fitFold = Below
