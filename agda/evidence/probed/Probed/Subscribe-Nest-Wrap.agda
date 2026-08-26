-- THE SUBSCRIBE DESCENT'S NEST BOUND AT THE THREE `*All` HEADS, which
-- nothing had ever instantiated.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-nest-merge
-- TARGET: subscribeE-nest-switch
-- TARGET: subscribeE-nest-exhaust
--
-- WHAT IS BEING TESTED, and at the STRONGEST reading of the statement:
-- every row fixes `W` at ZERO, the smallest burst width the grant can
-- be read at, so a green row here is stronger than the head asks for at
-- any `W` its own `descW` premise would permit.  The cap is the value's
-- own sync size, the smallest its `nestValOK?` premise admits; `B` is
-- `nestDᵉ` exactly, so the depth premise is `refl`; and the store is
-- `st-init`, whose `capsOK?` is pinned rather than assumed.
--
-- ONLY THE BURST CONJUNCT IS LOAD-BEARING HERE, and the reason is
-- structural rather than a gap in these programs.  `nodeNest` is ZERO by
-- definition on `switch-st` and on `exhaust-st`, so two of the three
-- heads cannot carry nesting at a node at all; and `mergeAll-st` reads
-- the maximum depth of its PENDING list, which is empty at subscribe
-- time -- an unlimited merge subscribes every inner at once, and a
-- LIMITED one over synchronous inners has already drained by the time
-- the descent returns.  `nodesOf` pins that zero at a limit of one and
-- at two nested layers, which is the row that would have caught a queue.
--
-- SO THE STORE HALVES ARE NOT COVERED, and a receipt claiming them
-- would be false: the second and third conjuncts are `0 ≤ _` in every
-- program reachable at `root` from an empty table, and what the head's
-- own risk names -- the drain, where a pending inner is paid for -- is
-- reached from a NON-EMPTY node table under a `from-inner` frame, which
-- is not this module.
--
-- THE DEPTH AXIS CANNOT REFUTE, which is the measurement rather than
-- the verdict.  Delivered nesting is exactly `k` at every head, while
-- the grant's BASE alone -- `B + suc m * U`, before the exponential
-- factor is applied at all -- is already 106 at `k = 1` and grows by
-- four per layer against the delivered one.  So the crossing rows the
-- map family has here do not exist: the bound is slack by construction
-- along the only axis these programs move, and the rows are marked
-- DEGENERATE on the exponent for that reason.
module Probed.Subscribe-Nest-Wrap where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
         nat̂; strmᵗ; syncSizeᵛ; syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

-- the payload the wrap HANDS BACK, so the delivered burst is nested
-- rather than flat: each inner is an observable of observables
wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

qS : ℕ → Closed Γ₂ (obs natᵗ)
qS k = switchAllᵉ (wrapped k)

qX : ℕ → Closed Γ₂ (obs natᵗ)
qX k = exhaustAllᵉ (wrapped k)

tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

lhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
lhs {t} e =
  let r = subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ t} (proj₁ r)))

-- the grant at `W = 0`, which is `nestB` at the smallest width the
-- statement can be read at, written out because `nestB` is sealed
rhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
rhs {t} e =
  let S = Caps.cSize (tight {obs t} e)
      m = syncSizeᵉ e
  in (2 ^ S) ^ m * (nestDᵉ e + suc m * nestUnit e slots)

burstAt : ∀ {t} (e : Closed Γ₂ t) → ℕ
burstAt {t} e =
  length (proj₁ (splitBurst {A = Val Γ₂ t}
    (proj₁ (subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e)))))

-- THE QUEUE, which is the only place a `*All` node carries nesting at
-- all: `mergeAll-st`'s nest is the maximum depth of its PENDING list, and
-- an unlimited merge subscribes every inner at once and pends nothing.
rM : ℕ → ℕ → Closed Γ₂ (obs natᵗ)
rM lim k = mergeAllᵉ (just lim) (wrapped k)

nodesOf : ∀ {t} (e : Closed Γ₂ t) → ℕ
nodesOf e =
  nodesMax (proj₂ (proj₂ (subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e))))

baseOf : ∀ {t} (e : Closed Γ₂ t) → ℕ
baseOf e = nestDᵉ e + suc (syncSizeᵉ e) * nestUnit e slots

-- the premises, pinned rather than assumed
prem : ∀ {t} (e : Closed Γ₂ t) → Set
prem {t} e =
  (nestValOK? (tight {obs t} e) (obs t) e ≡ true)
  × (capsOK? (tight {obs t} e) (sched-init e slots) (st-init e) ≡ true)

premM : prem (rM 1 1)
premM = refl , refl

premS : prem (qS 1)
premS = refl , refl

premX : prem (qX 1)
premX = refl , refl

-- NON-VACUITY: each descent hands back two values.  A row over an empty
-- burst would satisfy the first conjunct by having no values in it.
bursts : ℕ × ℕ × ℕ
bursts = burstAt (rM 1 1) , burstAt (qS 1) , burstAt (qX 1)

bursts≡ : bursts ≡ (2 , 2 , 2)
bursts≡ = refl

-- THE STORE HALVES, zero at every head and every layer -- the coverage
-- boundary above, pinned as a number rather than asserted
nodes : ℕ × ℕ × ℕ
nodes = nodesOf (rM 1 2) , nodesOf (qS 2) , nodesOf (qX 2)

nodes≡ : nodes ≡ (0 , 0 , 0)
nodes≡ = refl

-- WHAT THE DESCENT DELIVERS, one per layer at each head
emits : ℕ × ℕ × ℕ
emits = lhs (rM 1 0) , lhs (rM 1 1) , lhs (rM 1 2)

emits≡ : emits ≡ (0 , 1 , 2)
emits≡ = refl

emitsS : ℕ × ℕ
emitsS = lhs (qS 1) , lhs (qS 2)

emitsS≡ : emitsS ≡ (1 , 2)
emitsS≡ = refl

emitsX : ℕ × ℕ
emitsX = lhs (qX 1) , lhs (qX 2)

emitsX≡ : emitsX ≡ (1 , 2)
emitsX≡ = refl

-- THE GRANT'S BASE, before the exponential factor is applied at all
base≡ : baseOf (rM 1 1) ≡ 106
base≡ = refl

-- THE CONCLUSION at W = 0, at each head and at two layers.  DEGENERATE
-- on the exponent -- the base already carries these programs, so no row
-- here could have failed by the factor being too small.
fitsM : ((lhs (rM 1 1) ≤ᵇ rhs (rM 1 1)) ≡ true)
      × ((lhs (rM 1 2) ≤ᵇ rhs (rM 1 2)) ≡ true)
fitsM = refl , refl

fitsS : ((lhs (qS 1) ≤ᵇ rhs (qS 1)) ≡ true)
      × ((lhs (qS 2) ≤ᵇ rhs (qS 2)) ≡ true)
fitsS = refl , refl

fitsX : ((lhs (qX 1) ≤ᵇ rhs (qX 1)) ≡ true)
      × ((lhs (qX 2) ≤ᵇ rhs (qX 2)) ≡ true)
fitsX = refl , refl
