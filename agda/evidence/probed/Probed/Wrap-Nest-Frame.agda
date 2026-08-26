-- ══════════════════════════════════════════════════════════════════
-- THE `*All` HEADS AWAY FROM THE ROOT, AND FROM A NODE TABLE THAT IS
-- ALREADY CARRYING SOMETHING.
--
-- TARGET: subscribeE-nest-merge
-- TARGET: subscribeE-nest-switch
-- TARGET: subscribeE-nest-exhaust
--
-- WHY THIS AXIS.  `Probed.Subscribe-Nest-Wrap` reads all three heads at
-- `κ = root` from `st-init`, and says so: the store conjuncts are
-- `0 ≤ _` in every program reachable that way, and what the heads' own
-- risk names is a NON-EMPTY node table under a frame.  That is this
-- module.  The grant is the reason the axis is worth a row rather than
-- an argument: `G` is `nestB` at the caps size, the ambient program's
-- unit and the SUBTERM's sync size, and it mentions `κ` nowhere at all.
-- A frame's cost reaches the statement only through `descW`, which
-- bounds `W`, so a path that installs is paid for by a quantity the
-- grant reads at one remove.
--
-- THE `W = 0` READING, AND WHY IT STILL TRANSFERS.  Every row fixes the
-- grant at `W = 0`, which is smaller than the `W` these programs' own
-- `descW` premise forces -- `nestB` is `((2 ^ S) ^ suc W) ^ m * …`, so
-- it rises with `W` and clearing the smaller grant clears the larger.
-- That fact is true by inspection of a sealed body and is not a lemma
-- anywhere; the argument is stated where it is spent, at
-- `Probed.Subscribe-Nest-Wrap`.
--
-- WHAT IS LOAD-BEARING.  The incoming table is not a decoration: it
-- holds a merge node whose QUEUE carries a value three deep, so
-- `nodeNestAt` at that node reads 3 rather than zero going in and the
-- second and third conjuncts are no longer `0 ≤ _`.  The rows CAN
-- fail: a subscribe that installs under the frame something deeper
-- than both the incoming reading and the grant breaks them.
-- ══════════════════════════════════════════════════════════════════
module Probed.Wrap-Nest-Frame where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
         nat̂; strmᵗ; deferᵉ; syncSizeᵛ; syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init; EvalSt;
         Path; _↠_; thru-outer; mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; nestCapsOK?; nodeNestAt)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

-- the three heads, at the type the frame below consumes
oM : ℕ → Closed Γ₂ (obs natᵗ)
oM k = mergeAllᵉ (just 1) (wrapped k)

oS : ℕ → Closed Γ₂ (obs natᵗ)
oS k = switchAllᵉ (wrapped k)

oX : ℕ → Closed Γ₂ (obs natᵗ)
oX k = exhaustAllᵉ (wrapped k)

-- the ambient program, kept trivial so the unit is as small as it goes
prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

-- THE PATH: the head is subscribed UNDER a merge frame, not at the root
κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

-- THE TABLE IT STARTS FROM: a merge node whose queue holds a value
-- three deep, so the store conjuncts are not `0 ≤ _`.  It sits at an id
-- the FRAME does not claim -- put it at the frame's own node and the
-- subscribe overwrites it, and the rows go back to reading zero.
st₀ : EvalSt prog
st₀ = installNode 7 (mergeAll-st {t = natᵗ} (just 1) 1 (deepV 3 ∷ []) false)
                 (st-init prog)

tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

run : ∀ (o : Closed Γ₂ (obs natᵗ)) → _
run o = subscribeE gasBig o κ 0 0 (sched-init prog slots) st₀

-- the premises the head actually names, pinned rather than assumed
prem : (o : Closed Γ₂ (obs natᵗ)) → Set
prem o =
  (nestValOK? (tight {obs (obs natᵗ)} o) (obs (obs natᵗ)) o ≡ true)
  × (nestCapsOK? (tight {obs (obs natᵗ)} o) (sched-init prog slots) st₀ ≡ true)

premM : prem (oM 1)
premM = refl , refl

premS : prem (oS 1)
premS = refl , refl

premX : prem (oX 1)
premX = refl , refl

-- the grant at `W = 0`, written out because `nestB` is sealed
G : (o : Closed Γ₂ (obs natᵗ)) → ℕ
G o =
  let S = Caps.cSize (tight {obs (obs natᵗ)} o)
      m = syncSizeᵉ o
  in (2 ^ S) ^ m * (nestDᵉ o + suc m * nestUnit prog slots)

-- THE ARMING READING: what the table carries going in
armed : ℕ
armed = nodeNestAt 7 st₀

burstOf : (o : Closed Γ₂ (obs natᵗ)) → ℕ
burstOf o = nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ natᵗ} (proj₁ (run o))))

nodesOf : (o : Closed Γ₂ (obs natᵗ)) → ℕ
nodesOf o = nodesMax (proj₂ (proj₂ (run o)))

atOf : (o : Closed Γ₂ (obs natᵗ)) → ℕ
atOf o = nodeNestAt 7 (proj₂ (proj₂ (run o)))

figures : ℕ
figures = armed + 10 * burstOf (oM 1) + 100 * nodesOf (oM 1)
        + 1000 * atOf (oM 1) + 10000 * nodesOf (oS 1) + 100000 * nodesOf (oX 1)

figures≡ : figures ≡ 333313
figures≡ = refl

-- AND THE ROW WHERE THE SUBSCRIBE ITSELF INSTALLS.  The readings above
-- come out equal to what the table already held, so the incoming
-- summand carries them on its own and the grant is never asked for
-- anything.  A limited merge whose FIRST inner is a `deferᵉ` does not
-- finish inside the frame, so its limit is still spent when the descent
-- returns and the second inner is genuinely parked -- and then the
-- node's own queue is what the conjuncts read.
parkedOuter : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
parkedOuter k =
  ofᵉ (strmᵗ (deferᵉ (ofᵉ (strmᵗ (deepV 0) ∷ [])))
       ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

oP : ℕ → Closed Γ₂ (obs natᵗ)
oP k = mergeAllᵉ (just 1) (parkedOuter k)

premP : prem (oP 6)
premP = refl , refl

parked : ℕ
parked = nodesOf (oP 6) + 100 * atOf (oP 6) + 10000 * burstOf (oP 6)

parked≡ : parked ≡ 306
parked≡ = refl

-- THE CONJUNCTS THEMSELVES, at the head that installs
fitsP : ((burstOf (oP 6) ≤ᵇ G (oP 6)) ≡ true)
      × ((nodesOf (oP 6) ≤ᵇ nodesMax st₀ ⊔ G (oP 6)) ≡ true)
      × ((atOf (oP 6) ≤ᵇ armed ⊔ G (oP 6)) ≡ true)
fitsP = refl , refl , refl
