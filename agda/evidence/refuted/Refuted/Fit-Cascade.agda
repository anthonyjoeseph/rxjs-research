-- THE FIT IS NOT PRESERVED BY A CASCADE, AND THE GAP IT OPENS IS
-- UNBOUNDED.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- WHY PRESERVATION IS THE QUESTION AND NOT THE DOOR.  The door is
-- witnessed elsewhere and was repaired; what a proof of the drain leaf
-- needs is the fit at the state the drain hands its own recursive call,
-- so every step but the first applies the premise at a state a cascade
-- produced.  An invariant that holds at entry and is destroyed by one
-- arrival is not an invariant, and that is what these rows establish:
-- the crossing here happens at the FIRST arrival, from a tight entry.
--
-- THE STRUCTURAL LAW UNDERNEATH, which is what makes the witness small.
-- A `thru-outer` frame hands the inner the path BELOW itself, so an
-- inner attaches by `from-inner` — which the chain measure passes
-- through at zero.  A chain therefore carries one flattening edge for
-- each flattener whose OUTER SOURCE is still live along it, and nesting
-- flatteners over DATA stacks nothing.  The one shape that does stack
-- them is a flattener whose outer is itself late, i.e. a GATE: a defer
-- registers a `thru-outer` frame and leaves its body pending, so the
-- frame outlives the subscribe that made it.
--
-- AND THE READING CANNOT SEE THAT STACK, BECAUSE ITS GATE CLAUSE IS
-- CONSTANT.  The expression measure prices a defer at one without
-- reading its body — which is the clause that lets the descent keep its
-- recursion edge, and is defended on exactly those grounds where it is
-- defined.  So a gate OVER a flattener-over-a-gate reads one while the
-- chain the run reaches reads two, and each further turn of the same
-- crank adds one to the chain and nothing to the term.  The second
-- witness below is that crank turned once more: three against one.
--
-- WHAT THIS KILLS AND WHAT IT LEAVES.  The conclusion is untouched —
-- every program here runs dry-free, and the row pinning that is claimed
-- beside the crossings on purpose.  What is dead is the ROUTE: an
-- induction on the drain that carries the fit forward cannot, because
-- the fit is false one arrival in at a program the entry is perfectly
-- happy with.  Conditioning harder does not help either, since the gap
-- grows without bound in the program's own size while the term reading
-- stays at one.
--
-- AND THE OBVIOUS REPAIR IS THE ONE THE DESCENT FORBIDS.  Charging the
-- defer's body would close both crossings and would cost the descent
-- the edge the constant clause buys it.  So this is not an arithmetic
-- slip with a local fix: it is the tier's open question — whether one
-- reading can price what no frame hands the next one — arriving at the
-- premise rather than at the conclusion.
module Refuted.Fit-Cascade where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Source; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; obs; strmᵗ; ofᵉ;
  mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; ε; mapStep; flatten; hopOf; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; Chain; RegId; Sched; EvalSt; root;
  share-sink; _↠_; map-f; scan-f; take-f; from-inner; thru-outer;
  cascade; sched-next; subscribeE; rootWitness; sched-init; st-init;
  evaluate; hasDry)

----------------------------------------------------------------------
-- THE CURRENCY, WRITTEN OUT HERE RATHER THAN IMPORTED.  This is the
-- JOINING form the repair at the door installed, and it is what is
-- refuted: localised, the witness goes on naming the form it was taken
-- against, and a reading repaired to charge a gate's body makes the
-- rows below fail by name instead of quietly agreeing.
----------------------------------------------------------------------

chainRd′ : ∀ {n} {Γ : Ctx n} {s t} (ψ : Fin n → Rd₃) →
           Path Γ s t → Rd₃ → Rd₃
chainRd′ ψ root                    p = p
chainRd′ ψ (share-sink i)          p = p
chainRd′ ψ (map-f fn ↠ κ)          p = chainRd′ ψ κ (mapStep ψ ε p fn)
chainRd′ ψ (scan-f fn nid ↠ κ)     p = chainRd′ ψ κ (mapStep ψ ε p fn)
chainRd′ ψ (take-f nid ↠ κ)        p = chainRd′ ψ κ p
chainRd′ ψ (from-inner op a i ↠ κ) p = chainRd′ ψ κ p
chainRd′ ψ (thru-outer op nid ↠ κ) p = chainRd′ ψ κ (flatten p)

regsDepth′ : ∀ {n} {Γ : Ctx n} {t} (ψ : Fin n → Rd₃) →
             List (RegId × Source × Chain Γ t) → ℕ
regsDepth′ ψ []                   = 0
regsDepth′ ψ ((rid , src , c) ∷ r) =
  hopOf (chainRd′ ψ (proj₂ c) (0 , 0 , 0)) ⊔ regsDepth′ ψ r

HopFits′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
           Sched Γ → EvalSt e → Set
HopFits′ {e = e} sched st =
  let ψ = slotRd (Sched.slots sched) in
  regsDepth′ ψ (EvalSt.registry st) ≤ depthᵉ ψ e

----------------------------------------------------------------------
-- THE STATEMENT.  One arrival, taken through the drain's own step — the
-- same `sched-next` and the same `cascade`, in the same order — so the
-- pair it hands back is the pair the drain would have recursed on, not
-- a state written by hand.  A hand-built registry is what the sibling
-- witness at the other door spends, and it is refutation material of a
-- weaker kind; nothing here is constructed.
----------------------------------------------------------------------

stepOnce : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Sched Γ × EvalSt e → Sched Γ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

FitPreserved : Set
FitPreserved = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nextId : Id) (sched : Sched Γ) (st : EvalSt e) →
  HopFits′ sched st →
  HopFits′ (proj₁ (stepOnce {e = e} nextId (sched , st)))
           (proj₂ (stepOnce {e = e} nextId (sched , st)))

----------------------------------------------------------------------
-- THE PROGRAMS.  One slot, scripted with values arriving well past the
-- tick a gate's body is scheduled on, so the gate has closed over its
-- flattener by the time anything is delivered — a synchronous slot
-- would complete inside its own subscribe frame and leave a registry
-- whose comparison could not have failed.
--
-- `q₁` is a flattener whose outer is a gate, behind a second gate.
-- `q₃` is the same with one more flattener over the same late outer:
-- the crank that shows the gap is a rate rather than an off-by-one.
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
entry e ins =
  let (_ , sched , st) =
        subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
          (st-init e)
  in sched , st

carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ × EvalSt e → ℕ
carried (sched , st) = regsDepth′ (slotRd (Sched.slots sched)) (EvalSt.registry st)

term : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Sched Γ × EvalSt e → ℕ
term e (sched , _) = depthᵉ (slotRd (Sched.slots sched)) e

----------------------------------------------------------------------
-- THE CROSSING, PINNED ON BOTH SIDES AT BOTH POINTS.  The entry rows
-- are what make this a refutation of PRESERVATION rather than a second
-- witness at the door: the fit holds there, and TIGHTLY — one against
-- one, with no slack for a repair to hide in — and it is one arrival
-- that breaks it.  Either figure moving fails a row by name rather
-- than turning the witness into a quiet equality, which is the one way
-- a refutation of an inequality dies without saying so.
----------------------------------------------------------------------

e₁ s₁ : Sched Γ₁ × EvalSt q₁
e₁ = entry q₁ insLate
s₁ = stepOnce 1 e₁

carried-e₁ : carried e₁ ≡ 1                            -- LOAD-BEARING
carried-e₁ = refl

term-e₁ : term q₁ e₁ ≡ 1                               -- LOAD-BEARING
term-e₁ = refl

fit-e₁ : HopFits′ (proj₁ e₁) (proj₂ e₁)
fit-e₁ = ≤-refl

carried-s₁ : carried s₁ ≡ 2                            -- LOAD-BEARING
carried-s₁ = refl

term-s₁ : term q₁ s₁ ≡ 1                               -- LOAD-BEARING
term-s₁ = refl

fit-preserved-false : FitPreserved → ⊥
fit-preserved-false h with h 1 (proj₁ e₁) (proj₂ e₁) fit-e₁
... | s≤s ()

----------------------------------------------------------------------
-- AND THE GAP IS A RATE.  One more flattener over the same late outer
-- moves the carried reading to three while the term reading stays at
-- one, so no fixed slack in the premise repairs it and the question is
-- not how much to widen by.  The rows are pinned rather than spent:
-- the ⊥ above is already had, and what these buy is that it is not an
-- off-by-one.
----------------------------------------------------------------------

e₃ s₃ : Sched Γ₁ × EvalSt q₃
e₃ = entry q₃ insLate
s₃ = stepOnce 1 e₃

carried-e₃ : carried e₃ ≡ 1                            -- LOAD-BEARING
carried-e₃ = refl

term-e₃ : term q₃ e₃ ≡ 1                               -- LOAD-BEARING
term-e₃ = refl

carried-s₃ : carried s₃ ≡ 3                            -- LOAD-BEARING
carried-s₃ = refl

term-s₃ : term q₃ s₃ ≡ 1                               -- LOAD-BEARING
term-s₃ = refl

----------------------------------------------------------------------
-- AND IT IS THE GATE'S DOING AND NOT THE FLATTENER'S, WHICH IS WHAT
-- LOCALISES THE REPAIR.  Strip the outer defer from each program and
-- the reading becomes EXACT at the same states: two against two, three
-- against three, with the stack in plain view of a measure that has a
-- flattener to descend into.  So the chain is not manufacturing depth
-- and the addition is not the wrong arithmetic — both of which were
-- live readings of the crossings above, and both of which these rows
-- rule out.  What is left is the one clause that declines to look.
----------------------------------------------------------------------

u₁ : Closed Γ₁ natᵗ
u₁ = mergeAllᵉ nothing (deferᵉ obsSlot)

u₃ : Closed Γ₁ natᵗ
u₃ = mergeAllᵉ nothing (mergeAllᵉ nothing (deferᵉ obsSlot²))

carried-u₁ : carried (entry u₁ insLate) ≡ 2             -- LOAD-BEARING
carried-u₁ = refl

term-u₁ : term u₁ (entry u₁ insLate) ≡ 2                -- LOAD-BEARING
term-u₁ = refl

carried-u₃ : carried (entry u₃ insLate) ≡ 3             -- LOAD-BEARING
carried-u₃ = refl

term-u₃ : term u₃ (entry u₃ insLate) ≡ 3                -- LOAD-BEARING
term-u₃ = refl

----------------------------------------------------------------------
-- THE CONCLUSION IS INTACT, WHICH IS WHY THESE TWO ROWS ARE CLAIMED
-- BESIDE THE CROSSINGS.  Both programs run dry-free.  So what the
-- crossings kill is the premise's standing as an invariant and the
-- induction that would carry it, never the leaf's conclusion — and a
-- reader who took the crossings for a refutation of the tier's claim
-- would be reading them one statement too high.
----------------------------------------------------------------------

dry₁ : hasDry (evaluate 50 q₁ insLate) ≡ false         -- LOAD-BEARING
dry₁ = refl

dry₃ : hasDry (evaluate 50 q₃ insLate) ≡ false         -- LOAD-BEARING
dry₃ = refl
