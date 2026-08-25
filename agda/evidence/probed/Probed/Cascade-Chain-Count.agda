-- THE ENTRY WALK'S STORE GROWTH, CHARGED PER CHAIN.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
--
-- TWO STATEMENTS, ONE WALK, and that is why they share a file.  One says
-- the nodes map deepens at most once per chain the walk was handed; the
-- other says an arrival cannot present more chains than the entry width.
-- Both are read off the same `cascadeGo`, at the same arrival, on the
-- same families, so a row that moves one moves the other.
--
-- WHICH SIDE IS BLOCKED, since only one is.  The first statement is
-- premise-free and computes on both sides.  The second's CONCLUSION
-- computes -- `chainsOf` filters the registry, `capsBase` is a syntactic
-- reading -- but its `capsOK?` premise does not, reading a cap record no
-- instantiation terminates on, so those rows cannot certify that their
-- states are ones the target admits.  What a row here can do is REFUTE.
--
-- EVERY ROW IS LOAD-BEARING, AND THE AXIS IS THE ONE THAT KILLED THE
-- PREDECESSOR.  `progF w` registers `suc w` copies of one input, so an
-- arrival there presents `suc w` chains and both quantities are driven
-- directly.  A charge that counted MINTS instead was refuted on exactly
-- this sweep, quadratic against a linear width -- so a candidate that
-- does not hold at the crossing shape is no candidate.
--
-- TARGET: cascadeGo-nodes-chains
-- TARGET: chains-count-base
module Probed.Cascade-Chain-Count where

open import Data.List using (List; []; _++_; length; foldr)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _⊔_; _*_; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascadeLatch; cascadeGo; chainsOf; capsBase)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (nodeNest; nestSyn)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; insF; sucGU; sucGC; sucGF)

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
-- plus one `nestSyn` per chain.  This is the target's own conclusion,
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
      rhs = nodesMax stL + length ch * nestSyn e sl
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
      rhs = nodesMax stL + length ch * nestSyn e sl
  in lhs , rhs , (lhs ≤ᵇ rhs)

dupRow : ∀ {t} (e : Closed Γ₂ t) → ℕ → ℕ → ℕ × ℕ × Bool
dupRow e g k = let e₀ = entry e sl₁ g in readDup e sl₁ k (proj₁ e₀) (proj₂ e₀)

Dup1-fits : proj₂ (proj₂ (dupRow (progF 1 1) (sucGF 1 2 2 1 1) 1)) ≡ true
Dup1-fits = refl

Dup4-fits : proj₂ (proj₂ (dupRow (progF 1 1) (sucGF 1 2 2 1 1) 4)) ≡ true
Dup4-fits = refl

----------------------------------------------------------------------
-- READING TWO — the chain count against the entry width.  The width is
-- `capsBase`, which is what `realWidAt` reduces to at this index, so
-- this is the second target's conclusion verbatim.
----------------------------------------------------------------------

readK : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
      → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readK e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let k = length (chainsOf a st)
  in k , capsBase e sl , (k ≤ᵇ capsBase e sl)

kRow : ∀ {t} (e : Closed Γ₂ t) → ℕ → ℕ × ℕ × Bool
kRow e g = let e₀ = entry e sl₁ g in readK e sl₁ (proj₁ e₀) (proj₂ e₀)

K22-fits : proj₂ (proj₂ (kRow (progF 22 1) (sucGF 1 2 2 22 1))) ≡ true
K22-fits = refl

K1-fits : proj₂ (proj₂ (kRow (progF 1 1) (sucGF 1 2 2 1 1))) ≡ true
K1-fits = refl

KU-fits : proj₂ (proj₂ (kRow (progU 2 2) (sucGU 1 2 2 2 2))) ≡ true
KU-fits = refl

KC-fits : proj₂ (proj₂ (kRow (progC 1 2 2) (sucGC 1 2 2 1 2 2))) ≡ true
KC-fits = refl
