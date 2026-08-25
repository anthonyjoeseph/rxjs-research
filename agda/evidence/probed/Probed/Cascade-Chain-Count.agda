-- THE ENTRY WALK'S STORE GROWTH, CHARGED PER CHAIN.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
--
-- NOTHING IS BLOCKED HERE, which is unusual in this neighbourhood and
-- is why the rows are worth taking: the target is premise-free and both
-- sides compute off the evaluator, so a row that reads false is a
-- refutation outright rather than a candidate modulo a cap record.
--
-- EVERY ROW IS LOAD-BEARING, AND THE AXIS IS THE ONE THAT KILLED THE
-- PREDECESSOR.  `progF w` registers `suc w` copies of one input, so an
-- arrival there presents `suc w` chains and both quantities are driven
-- directly.  A charge that counted MINTS instead was refuted on exactly
-- this sweep, quadratic against a linear width -- so a candidate that
-- does not hold at the crossing shape is no candidate.
--
-- AND THE ADVERSARIAL PATH IS SWEPT TOO, which is the axis that killed
-- the charge this one replaced: the target quantifies over every path
-- of the context, so a frame carrying a wrap the program never mentions
-- is a legitimate instantiation and not a hand-built state.  The last
-- reading below hands the step exactly that, and the path-denominated
-- charge covers it where a program-denominated one does not.
--
-- TARGET: chainStep-nodes
module Probed.Cascade-Chain-Count where

open import Data.List using (List; []; _∷_; _++_; length; foldr)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _⊔_; _*_; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; nat̂)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascadeLatch; cascadeGo; chainsOf; chainStep; Arrival; arrTy; arrVal; RegId; Path;
         _↠_; scan-f; map-f)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (nodeNest; pathNestD; chainsNestD)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; progW; foldD; insF; sucGU; sucGC; sucGF; sucGW)

----------------------------------------------------------------------
-- The walk, taken at the arrival the root subscribe leaves behind,
-- which is the index both targets are stated at.
----------------------------------------------------------------------

entry : ∀ {t} (e : Closed Γ₂ t) → Slots Γ₂ → ℕ → Sched Γ₂ × EvalSt e
entry e sl g =
  let r = subscribeE (gasPad g g0) e root 0 0 (sched-init e sl) (st-init e)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

sl₁ : Slots Γ₂
sl₁ = insF 1 2 2

nodesMax : ∀ {t} {e : Closed Γ₂ t} → EvalSt e → ℕ
nodesMax st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

----------------------------------------------------------------------
-- READING ONE — the nodes map after the walk, against the map before it
-- plus one payload-and-chains charge per chain.  This is the target's own conclusion,
-- with nothing weakened: the parent charges the whole store measure on
-- the right, and the store measure dominates the nodes map.
----------------------------------------------------------------------

readCh : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
       → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readCh e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      ch  = chainsOf a st
      g   = cascadeGo a 1 ch sd stL
      lhs = nodesMax (proj₂ (proj₂ g))
      rhs = nodesMax stL + length ch * (nestDᵛ (arrTy a) (arrVal a) + chainsNestD ch)
  in lhs , rhs , (lhs ≤ᵇ rhs)

chRow : ∀ {t} (e : Closed Γ₂ t) → ℕ → ℕ × ℕ × Bool
chRow e g = let e₀ = entry e sl₁ g in readCh e sl₁ (proj₁ e₀) (proj₂ e₀)

-- THE CROSSING SHAPE, where the mint-counting predecessor reads 713
-- against 690.  If the chain-counting charge is also short here there
-- is no counting route at all.
Ch22-fits : proj₂ (proj₂ (chRow (progF 22 1) (sucGF 1 2 2 22 1))) ≡ true
Ch22-fits = refl

-- DELIVERY ON EVERY CHAIN, the arm `progC` skips.
Ch1-fits : proj₂ (proj₂ (chRow (progF 1 1) (sucGF 1 2 2 1 1))) ≡ true
Ch1-fits = refl

-- THE BOUNDED DRAIN, where every release is a subscription and one
-- chain installs many nodes -- the shape a per-chain charge has most to
-- lose on.
ChU-fits : proj₂ (proj₂ (chRow (progU 2 2) (sucGU 1 2 2 2 2))) ≡ true
ChU-fits = refl

-- THE SKIP BRANCH, where the selection outruns the deliveries, so the
-- charge is paid for chains that store nothing.
ChC-fits : proj₂ (proj₂ (chRow (progC 1 2 2) (sucGC 1 2 2 1 2 2))) ≡ true
ChC-fits = refl

----------------------------------------------------------------------
-- AND THE CHAIN LIST IS A FREE ARGUMENT OF THE TARGET, so the honest
-- selection is not the adversarial case.  Handing the walk the
-- arrival's own chains over and over drives the left side and the right
-- side together, and the right side moves faster: a whole `nestSyn` per
-- chain against whatever one more pass through the same chains adds to
-- a MAX.
----------------------------------------------------------------------

rep : ∀ {A : Set} → ℕ → List A → List A
rep 0       xs = []
rep (suc k) xs = xs ++ rep k xs

readDup : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂) → ℕ
        → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readDup e sl k sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      ch  = rep k (chainsOf a st)
      g   = cascadeGo a 1 ch sd stL
      lhs = nodesMax (proj₂ (proj₂ g))
      rhs = nodesMax stL + length ch * (nestDᵛ (arrTy a) (arrVal a) + chainsNestD ch)
  in lhs , rhs , (lhs ≤ᵇ rhs)

dupRow : ∀ {t} (e : Closed Γ₂ t) → ℕ → ℕ → ℕ × ℕ × Bool
dupRow e g k = let e₀ = entry e sl₁ g in readDup e sl₁ k (proj₁ e₀) (proj₂ e₀)

Dup1-fits : proj₂ (proj₂ (dupRow (progF 1 1) (sucGF 1 2 2 1 1) 1)) ≡ true
Dup1-fits = refl

Dup4-fits : proj₂ (proj₂ (dupRow (progF 1 1) (sucGF 1 2 2 1 1) 4)) ≡ true
Dup4-fits = refl

----------------------------------------------------------------------
-- READING TWO — the leaf itself, ONE chain's step.  The rows above take
-- the assembly, which is a real body over this and so refutable through
-- it; this one takes the charge where it is actually claimed, at the
-- head of the arrival's own selection.
----------------------------------------------------------------------

stepOn : ∀ {t} {e : Closed Γ₂ t} (sl : Slots Γ₂) (a : Arrival Γ₂)
       → List (RegId × Path Γ₂ (arrTy a) t) → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
stepOn sl a []            sched st = 0 , 0 , false
stepOn {e = e} sl a ((rid , c) ∷ _) sched st =
  let r   = chainStep 1 a c sched st
      lhs = nodesMax (proj₂ (proj₂ r))
      rhs = nodesMax st + (nestDᵛ (arrTy a) (arrVal a) + pathNestD c)
  in lhs , rhs , (lhs ≤ᵇ rhs)

readS : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
      → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readS e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
  in stepOn sl a (chainsOf a stL) sd stL

sRow : ∀ {t} (e : Closed Γ₂ t) → ℕ → ℕ × ℕ × Bool
sRow e g = let e₀ = entry e sl₁ g in readS e sl₁ (proj₁ e₀) (proj₂ e₀)

S22-fits : proj₂ (proj₂ (sRow (progF 22 1) (sucGF 1 2 2 22 1))) ≡ true
S22-fits = refl

S1-fits : proj₂ (proj₂ (sRow (progF 1 1) (sucGF 1 2 2 1 1))) ≡ true
S1-fits = refl

SU-fits : proj₂ (proj₂ (sRow (progU 2 2) (sucGU 1 2 2 2 2))) ≡ true
SU-fits = refl

SC-fits : proj₂ (proj₂ (sRow (progC 1 2 2) (sucGC 1 2 2 1 2 2))) ≡ true
SC-fits = refl

-- AND THE WRAPPING FAMILY, which is the only one here whose stored
-- value is OBSERVABLE-typed: `progW`'s accumulator is re-merged into
-- itself `suc ww` times per emission, so `nodeNest` of its scan node is
-- the one quantity in the store that a step can actually deepen.  Every
-- other family holds a `natᵗ` accumulator, whose nest is zero however
-- long the run -- so without these rows the sweep drives the charge
-- against a left side pinned at 0 and could not fail.  Here it reads 3
-- against 8, so both halves move.
SW-fits : proj₂ (proj₂ (sRow (progW 1 0 0) (sucGW 1 2 2 1 0 0))) ≡ true
SW-fits = refl

ChW-fits : proj₂ (proj₂ (chRow (progW 1 0 0) (sucGW 1 2 2 1 0 0))) ≡ true
ChW-fits = refl

-- ONE MORE CHAIN, so the arrival presents two chains into the same deepening
-- accumulator and the per-chain charge has to cover each of them.
ChW2-fits : proj₂ (proj₂ (chRow (progW 1 1 0) (sucGW 1 2 2 1 1 0))) ≡ true
ChW2-fits = refl

----------------------------------------------------------------------
-- READING THREE -- THE PATH IS A FREE ARGUMENT TOO, and unlike the
-- chain list it is not a list of things the run produced: the target
-- quantifies over EVERY path of the context, while the charge names a
-- quantity of `e` alone.  A scan frame carrying a deep wrap is then a
-- node the step installs at whatever depth the frame asks for, against
-- a program that never mentions it.
----------------------------------------------------------------------

advPath : ℕ → Path Γ₂ natᵗ natᵗ
advPath d = scan-f (foldD d) 7 ↠ (map-f (nat̂ 0) ↠ root)

advArr : Arrival Γ₂
advArr = record { tick = 0 ; ordinal = 0 ; source = 1 ; elemTy = natᵗ
                ; payload = 0 ; isLast = false }

readAdv : (e : Closed Γ₂ natᵗ) (sl : Slots Γ₂) → ℕ
        → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readAdv e sl d sched st =
  let r   = chainStep 1 advArr (advPath d) sched st
      lhs = nodesMax (proj₂ (proj₂ r))
      rhs = nodesMax st + (nestDᵛ {Γ = Γ₂} (arrTy advArr) (arrVal advArr) + pathNestD (advPath d))
  in lhs , rhs , (lhs ≤ᵇ rhs)

advRow : ℕ → ℕ × ℕ × Bool
advRow d = let e₀ = entry (progF 1 1) sl₁ (sucGF 1 2 2 1 1)
           in readAdv (progF 1 1) sl₁ d (proj₁ e₀) (proj₂ e₀)

Adv-fits : proj₂ (proj₂ (advRow 9)) ≡ true
Adv-fits = refl
