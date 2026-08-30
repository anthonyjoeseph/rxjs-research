-- ══════════════════════════════════════════════════════════════════
-- THE SIGHTED FACE'S ENTRY FIT PRICES THE PAYLOAD AND NOT THE SLOTS
-- IT NAMES, so `sight-all-fit` is FALSE as stated.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  Subscribing the payload of an `*All` head
-- hands back a burst, and every inner in it is granted
-- `2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))` -- a tower in the
-- payload's own sync size, times the path it is subscribed under.
-- Every term of that is read off the payload's SYNTAX.
--
-- WHERE IT BREAKS.  A payload may emit a slot reference: `ofᵉ (input i
-- ∷ [])` is three constructors whatever the slot holds, so both terms
-- of the grant are pinned by the arrival and the grant is the constant
-- sixteen.  Subscribing the emitted inner runs the slot's DEFINITION,
-- and a substituting layer doubles what comes back.  The rows below
-- deliver `8 16 32 64` against a grant that does not move: the third
-- layer meets it exactly and the fourth is double it, so this is a
-- CROSSING and not a scale error, and every layer past it widens the
-- gap without bound.
--
-- WHAT THE REPAIR HAS TO CARRY, and it is already in the consumer.
-- Every other bound on this face carries a `k * slotWrapSum` summand
-- for exactly this reason: `inputsBelowᵉ` bounds WHICH slots a term
-- may name, and the wrap sum is what pays for what they hold.  The
-- ceiling this fit is spent under already has that summand; the grant
-- does not, and widening the grant to match it costs the consumer
-- nothing, since a fit is a hypothesis there.
--
-- WHAT THIS DOES NOT KILL.  Nothing about the DESCENT half is touched
-- -- the walk leaf reads the fit rather than establishing it, and a
-- wider grant is a weaker hypothesis for it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Sight-All-Fit-Slot where

open import Data.Bool using (T)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Exp
  using (Ctx; Closed; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ; caseᵗ; inlᵗ; input;
  inputsBelowᵉ; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ;
         thruConsume; subscribeE; mintNode; installNode;
         sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; allFresh; slotWrapSum)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; pushFitOK)

-- an OBSERVABLE-typed slot, which is the only kind with depth to hand
-- back, and necessarily a `shared` one: scripted slots carry data only
Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

gas : Gas
gas = gasPad 400 g0

-- the payload lands in the step function AND in the source it maps
-- over, so one application doubles what is emitted
dup : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

dDup : ℕ → Closed Γₛ (obs natᵗ)
dDup zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
dDup (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup k) ∷ [])))

-- `inputsBelowᵉ` does not reduce at a variable depth, so the readings
-- are taken of a DEFINITION and each row supplies its own `tt`
sl : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Slots Γₛ
sl d ok fzero = shared d {ok = ok}

prog : Closed Γₛ (obs natᵗ)
prog = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

sched : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Sched Γₛ
sched d ok = sched-init prog (sl d ok)

-- the payload is a single emission of the SLOT REFERENCE: three
-- constructors, and every term of the grant is read off them
b : Closed Γₛ (obs (obs natᵗ))
b = ofᵉ (strmᵗ (input fzero) ∷ [])

κ : Path Γₛ (obs natᵗ) (obs natᵗ)
κ = root

st : EvalSt prog
st = st-init prog

nidOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → _
nidOf d ok = proj₁ (mintNode (sched d ok))

runOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → _
runOf d ok =
  subscribeE gas b (thru-outer mergeAllᵒ (nidOf d ok) ↠ κ) 0 0
    (proj₂ (mintNode (sched d ok)))
    (installNode (nidOf d ok) (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

deliveredOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
deliveredOf d ok =
  nestDᵛˢ (proj₁ (thruConsume gas mergeAllᵒ (nidOf d ok) κ 0 0
                    (input fzero)
                    (proj₁ (proj₂ (runOf d ok)))
                    (proj₂ (proj₂ (runOf d ok)))))

----------------------------------------------------------------------
-- THE PREMISE THE HEAD CARRIES, which a refutation has to meet: the
-- payload names slot zero and nothing above it
----------------------------------------------------------------------

okb : T (inputsBelowᵉ 1 b)
okb = tt

----------------------------------------------------------------------
-- THE ARRIVAL PINS BOTH TERMS OF THE GRANT
----------------------------------------------------------------------

G : ℕ
G = 2 ^ syncSizeᵉ b * (pathNestD κ + suc (nestDᵉ b))

G≡16 : G ≡ 16
G≡16 = refl

----------------------------------------------------------------------
-- THE COLUMN: delivered `8 16 32 64` against a grant that does not move
----------------------------------------------------------------------

delivered : ℕ
delivered = deliveredOf (dDup 3) tt + 100 * deliveredOf (dDup 4) tt
          + 10000 * deliveredOf (dDup 5) tt + 1000000 * deliveredOf (dDup 6) tt

delivered≡ : delivered ≡ 64321608
delivered≡ = refl

delivered₆≡64 : deliveredOf (dDup 6) tt ≡ 64
delivered₆≡64 = refl

----------------------------------------------------------------------
-- AND THE SUMMAND THE CONSUMER ALREADY CARRIES PAYS FOR IT, which is
-- what makes this a repair and not merely a refutation
----------------------------------------------------------------------

repaired : ℕ
repaired = G + 1 * slotWrapSum (Sched.slots (sched (dDup 6) tt))

repaired-holds : deliveredOf (dDup 6) tt ≤ repaired
repaired-holds = ≤ᵇ⇒≤ _ _ tt

sight-all-fit-slot-absurd :
  pushFitOK G gas mergeAllᵒ (nidOf (dDup 6) tt) κ 0 0
    (proj₁ (runOf (dDup 6) tt))
    (proj₁ (proj₂ (runOf (dDup 6) tt)))
    (proj₂ (proj₂ (runOf (dDup 6) tt))) → ⊥
sight-all-fit-slot-absurd fit =
  ≤⇒≤ᵇ (subst (λ z → deliveredOf (dDup 6) tt ≤ z) G≡16
          (proj₁ (proj₁ fit)))
