-- A REGISTERED CHAIN'S OWN FRAMES DEEPEN THE PAYLOAD, AND THE SHARE'S
-- PREMISE BOUNDS ONLY WHAT ENTERS IT.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- THE SHAPE OF THE GAP.  `share-chain-hop` asserts the walk's own
-- hypothesis package at every admitted chain, and it is given exactly
-- one thing: the hop the DISPATCHED VALUE carries fits under the store
-- bound.  But the package is read along the chain, and a chain's frames
-- move the payload before its flattener is reached — a fold re-wraps
-- its accumulator, so the reading at the frame AFTER the fold is the
-- fold's own and not the value's.  Nothing in the hypothesis mentions
-- the chain, so no bound on what enters can bound what the chain has
-- made of it by the time the descent is asked for.
--
-- THE WITNESS IS THE SMALLEST SHARE THAT FOLDS.  One consumer, whose
-- scan seeds an observable accumulator and re-wraps it once per
-- delivery, registered on a share over a cold script.  A numeral is
-- dispatched, so the entering payload reads nought on both halves and
-- the premise is satisfied at the FLOOR — there is no bound to make
-- tighter.  The store is the machine's own, off a real subscribe, and
-- it reads one: exactly what the fold's seed installed.  The chain's
-- own flattener is then asked for a rank of two.
--
-- AND THE STORE CANNOT BE THE REPAIR, WHICH IS WHY THE FIGURES ARE
-- CLAIMED IN A PAIR.  The bound the walk joins in is the store at the
-- state the chain is ENTERED under, and that state is the subscribe
-- state: the fold has installed its seed and nothing has arrived.  So
-- the number the chain is held to is fixed before the chain runs, while
-- the number it needs is a function of the chain — and one more fold
-- layer moves the second without moving the first.
--
-- WHAT THIS DOES NOT KILL.  Not the walk, and not the share arm: the
-- dispatch's fold is a body and the sink reduces to one obligation per
-- admitted chain, which is right.  What is refuted is that obligation
-- being derivable from the entering payload alone.  A true form has to
-- carry the registry's own reading — the fact the entry invariant knows
-- about the chains a share admits — into the statement, and that fact
-- appears in none of the hypotheses here.
--
-- AND THE MACHINE IS NOT DRY AT THIS WITNESS, WHICH IS THE WHOLE
-- DIAGNOSIS.  The rank a dispatch is actually entered under is the
-- door's, and the door's is a SUM whose first summand is the term
-- depth — five here, against the two the chain asks for.  So the
-- refuted point is legal under the hypothesis as written and
-- unreachable at every call site: what is too weak is the premise, not
-- the claim.  A row of this file going green after a repair therefore
-- means the repair carried the door's bound inward; a row going red
-- means it weakened the conclusion instead.
module Refuted.Share-Chain where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; _<_; _∸_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (lookup) renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Val; Fn; Tm; natᵗ; obs; _×ᵗ_;
  strmᵗ; ofᵉ; scanᵉ; mergeAllᵉ; input; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; root; shareAdmit;
  subscribeE; rootWitness; rootTri; sched-init; st-init; stHop)
open import Verify-Rank-Sufficient.Push-Carried using (mapRd)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Path-Fits using (ShareHop)

----------------------------------------------------------------------
-- THE STATEMENT, RESTATED.  The obligation is IMPORTED rather than
-- spelled out: what is refuted is the leaf's choice of hypothesis, not
-- the walk's package, so a repair that changes the package must make
-- this file fail to typecheck rather than leave it quietly green.
----------------------------------------------------------------------

ShareChainHop : Set
ShareChainHop = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} {lo}
  (ac : Acc _≺_ τ) (acl : Acc _<_ (n ∸ lo)) (id : Id) (now : Tick)
  (i : Fin n) (below : lo ≤ toℕ i)
  (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) → proj₂ Rin ≤ Rst →
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sd : Sched Γ) (st : EvalSt e) →
  ShareHop {e = e} ac acl id now i below ψ Rin Rst vals fin sd st

----------------------------------------------------------------------
-- THE HARNESS.  Slot zero is a cold script; slot one is a SHARE over
-- it, so the single consumer registers on one source.  The consumer
-- folds into an OBSERVABLE accumulator, which is what puts a reading
-- between the dispatched value and the chain's own flattener.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

ins : Slots Γ₂
ins zero       = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ []))
ins (suc zero) = shared (input zero)

deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₂ [] [] [] (obs natᵗ)
seed = strmᵗ (mergeAllᵉ nothing
         (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

cons : Tm Γ₂ [] [] [] (obs natᵗ)
cons = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen seed (input (suc zero))))

prog : Closed Γ₂ natᵗ
prog = mergeAllᵉ nothing (ofᵉ (cons ∷ []))

ψ₀ : Fin 2 → Rd₃
ψ₀ = slotRd ins

ac₀ : Acc _≺_ (rootTri prog ins)
ac₀ = rootWitness prog ins

-- the subscribe state: the fold has installed its seed and no arrival
-- has yet run, which is the state a dispatch is taken at
sd₀ : Sched Γ₂
sd₀ = proj₁ (proj₂ (subscribeE {lo = 2} ac₀ prog root 0 0
                     (sched-init prog ins) (st-init prog)))

st₀ : EvalSt prog
st₀ = proj₂ (proj₂ (subscribeE {lo = 2} ac₀ prog root 0 0
                     (sched-init prog ins) (st-init prog)))

vals₀ : List ℕ
vals₀ = 3 ∷ []

----------------------------------------------------------------------
-- THE CROSSING, PINNED ON BOTH SIDES.  An inequality refutation dies
-- quietly when a repair enlarges the right side, so each figure is
-- claimed by name: the dispatch reaches a non-empty registry, the store
-- the chain is held to reads one, and the chain's own payload at its
-- flattener reads one — so the rank asked for is two against a bound of
-- one.
----------------------------------------------------------------------

-- a row over an empty admitted list would be the `⊤` arm, which asserts
-- nothing at all
regs-is : length (shareAdmit (suc zero) (EvalSt.registry st₀)) ≡ 1
regs-is = refl                                         -- LOAD-BEARING

store-is : stHop ψ₀ st₀ ≡ 1                            -- LOAD-BEARING
store-is = refl

-- what the chain has made of the dispatched value by the time its own
-- flattener is reached: the fold's accumulator, not the numeral
chain-is : proj₂ (mapRd ψ₀ (0 , 0) deepen) ≡ 1         -- LOAD-BEARING
chain-is = refl

-- what the DOOR supplies as the store bound at this very witness: the
-- term depth is one summand of `arrivalRank`, and it alone is five
-- against the two the chain asks for
termFig : ℕ
termFig = depthᵉ ψ₀ prog

termFig-is : termFig ≡ 5                               -- LOAD-BEARING
termFig-is = refl

-- THE CHAIN IS TAKEN AT THE BOTTOM FLOOR, which is where a share's own
-- consumer stands: the descent the dispatch peels is the distance from
-- that floor to the top of the telescope, and the sink at index one
-- cuts it.  Nothing here turns on the choice — the crossing is the
-- store against the chain's reading, and the floor moves neither.
share-chain-hop-false : ShareChainHop → ⊥
share-chain-hop-false h
  with proj₁ (proj₁ (h {lo = 0} ac₀ (<-wellFounded-fast 2) 0 0 (suc zero) z≤n
                       ψ₀ (0 , 0) (stHop ψ₀ st₀)
                       z≤n vals₀ false sd₀ st₀))
... | s≤s ()
