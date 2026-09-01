-- ══════════════════════════════════════════════════════════════════
-- ONE CHAIN DOES NOT LEAVE THE REGISTRY PRICED AT THE CAP IT ENTERED
-- ON, AND WHAT BREAKS IS THE LENGTH LEDGER RATHER THAN ANY SIZE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A whole chain takes a registry priced
-- under a cap to a registry priced under the SAME cap, given that the
-- arrival fits the cap and the walked path is priced by it.
--
-- WHERE IT BREAKS.  A subscribing frame does not register the path it
-- was walking: it swaps its own head for a `from-inner` and pushes one
-- frame per operator of the inner observable on top, so what lands in
-- the registry is LONGER than what was walked.  `pathSz?` charges a
-- length -- `suc (pathLen tail) ≤ᵇ B` at every frame -- and a cap that
-- admits a chain of length `B` has nothing left to pay the inner with.
--
-- AND THE ARRIVAL'S SIZE PREMISE IS WHAT BUYS THE EXTRA FRAMES, WHICH
-- IS WHY NO READING REPAIRS THIS.  `sizeᵛ` at an observable IS `sizeᵉ`,
-- so the premise bounds the inner's syntax by the cap -- and an inner
-- that FITS the cap still contributes its operator count to the
-- registered path's length.  The two premises together therefore admit
-- a registered chain of nearly twice the cap, so the repair is a
-- LEVEL, which `sizeStep` pays for, and not a further hypothesis.
--
-- WHAT THIS COSTS UPSTREAM.  The plan this leaf carried was a
-- COLLAPSE: the fold beneath it reports at an accumulated level, and
-- the chain door was to bring that back to the entry cap.  There is no
-- such collapse -- one chain already leaves the entry cap, at a gap
-- that grows with the inner -- and the cascade fold spends this leaf
-- once per chain, feeding each output registry in as the next chain's
-- premise.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Regs-Cap where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; s≤s; z≤n)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Id; hot)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; input; mapᵉ;
  varᵗ; sizeᵛ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Path; root; _↠_;
  thru-outer; take-f; mergeAllᵒ; mergeAll-st; chainStep; arrTy; arrVal;
  sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
ChainStepRegsSz : Set
ChainStepRegsSz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  1 ≤ B →
  sizeᵛ (arrTy a) (arrVal a) ≤ B →
  pathSz? B path ≡ true →
  regsSz? B (EvalSt.registry st) ≡ true →
  regsSz? B (EvalSt.registry (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

-- the inner the outer frame consumes: two operators over a leaf, so
-- subscribing it pushes two frames before it reaches the leaf that
-- registers -- and its whole syntax is five nodes, under the cap
inner : Val Γ₁ (obs natᵗ)
inner = mapᵉ (varᵗ (here refl)) (mapᵉ (varᵗ (here refl)) (input fzero))

a : Arrival Γ₁
a = record { tick = 0 ; ordinal = 0 ; source = 0
           ; elemTy = obs natᵗ ; payload = inner ; isLast = false }

-- a chain exactly as long as the cap admits, and priced by it
chain : Path Γ₁ (obs natᵗ) natᵗ
chain = thru-outer mergeAllᵒ 0
      ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ root)))))

-- the node a `mergeAllᵉ` subscribe installs, with no lane taken
st₀ : EvalSt e₁
st₀ = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (st-init e₁)

after : EvalSt e₁
after = proj₂ (proj₂ (chainStep 0 a chain (sched-init e₁ sl₁) st₀))

B : ℕ
B = 6

-- the two figures the premises pin: the inner is under the cap and the
-- walked chain is exactly at it
figures : List ℕ
figures = sizeᵛ (obs natᵗ) inner ∷ pathLen chain ∷ []

figures≡ : figures ≡ 5 ∷ 6 ∷ []
figures≡ = refl

-- and the one the conclusion has to price: the head is swapped for a
-- `from-inner` and the inner's two operators are pushed on top
regLens : List ℕ
regLens = map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry after)

regLens≡ : regLens ≡ 8 ∷ []
regLens≡ = refl

premSz : sizeᵛ (obs natᵗ) inner ≤ B
premSz = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

premPath : pathSz? B chain ≡ true
premPath = refl

premReg : regsSz? B (EvalSt.registry st₀) ≡ true
premReg = refl

row : Bool
row = regsSz? B (EvalSt.registry after)

row≡false : row ≡ false
row≡false = refl

chain-step-regs-cap-absurd : ChainStepRegsSz → ⊥
chain-step-regs-cap-absurd pr =
  f≡t (trans (sym row≡false)
             (pr {e = e₁} B a 0 chain (sched-init e₁ sl₁) st₀
                 (s≤s z≤n) premSz premPath premReg))
