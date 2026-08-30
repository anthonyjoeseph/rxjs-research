-- ══════════════════════════════════════════════════════════════════
-- THE BURST'S ARRIVALS ARE NOT INSIDE THE HEAD'S OWN SIZE CAP, so
-- both stream leaves of the `*All` burst are FALSE at a map that
-- names its payload twice.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENTS SAID.  Every value the wrapped body hands the
-- outer is admissible at the SAME cap the head itself fits under --
-- written size for the admissibility leaf, and the size-and-width key
-- for the width leaf.
--
-- WHERE IT BREAKS.  The premises read the head's SYNTAX: its sync size
-- and its closure size, each counting a bound variable as one.  An
-- emitted VALUE is that syntax with the payload SUBSTITUTED IN, and a
-- step function naming its payload twice returns roughly twice the
-- payload while contributing a constant to the head.  So the body's
-- own arrival already exceeds the cap the head satisfies, and the gap
-- grows with the payload rather than with anything the premises see.
--
-- WHY IT IS THE FLAT CAP AND NOT THE PROGRAM.  The caps face charges a
-- descent through a `frameStep`, so the cap it reads a returned burst
-- at is LARGER than the one it entered with; the nest face keeps one
-- `c` across the whole walk because its grant is keyed on `cSize` and
-- a stepped key is a bigger grant than the parent owes.  Those two
-- cannot both hold of the same stream, and this is the witness that
-- says which one the stream side has to give up.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here touches the state half: the
-- caps-preservation walk concludes about the node table alone and is
-- unaffected, and the frame-width and queue leaves beside these two
-- read no value size at all.
-- ══════════════════════════════════════════════════════════════════
module Refuted.PushVals-Adm-Map where

open import Data.Bool using (Bool; true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; InstEmit)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ;
         syncSizeᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (splitEvents; root; sched-init; st-init; subscribeE; mintNode; EvalSt; Sched;
         Stream; _↠_; thru-outer; mergeAllᵒ; installNode)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestCapsOK?; pushValsAdmOK; pushValsWidOK;
         allWrap; allFresh)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

-- the step function names its payload on both arms of a merge, so the
-- value it returns is twice the value it was handed, plus a constant
dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dupFn = strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

bigV : Val Γ₂ (obs natᵗ)
bigV = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
            nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

body : Closed Γ₂ (obs natᵗ)
body = mapᵉ dupFn (ofᵉ (strmᵗ bigV ∷ []))

lim : Maybe ℕ
lim = nothing

head : Closed Γ₂ natᵗ
head = allWrap mergeAllᵒ lim body

-- the cap is the head's own written size, which is what the two size
-- premises ask for and all they ask for; the width and registry
-- fields are set wide so nothing but the SIZE half can be doing the
-- work
cap : Caps
cap = caps (syncSizeᵛ (obs natᵗ) head) 99 99

sched₀ : Sched Γ₂
sched₀ = sched-init head slots

st₀ : EvalSt head
st₀ = st-init head

nid : ℕ
nid = proj₁ (mintNode sched₀)

res : Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt head
res = subscribeE gasBig body (thru-outer mergeAllᵒ nid ↠ root) 0 0
        (proj₂ (mintNode sched₀))
        (installNode nid (allFresh natᵗ mergeAllᵒ lim) st₀)

W : ℕ
W = descW gasBig head root 0 0 sched₀ (st-init head)

-- the premises, pinned true where the rows run rather than assumed
prems-map : Bool × Bool × Bool
prems-map = nestCapsOK? cap sched₀ st₀
      , nestValOK? cap (obs natᵗ) head
      , nestClosOK? cap slots head

prems-map≡ : prems-map ≡ (true , true , true)
prems-map≡ = refl

AdmStmt : Set
AdmStmt =
  Sched.slots sched₀ ≡ slots →
  nestCapsOK? cap sched₀ st₀ ≡ true →
  nestValOK? cap (obs natᵗ) head ≡ true →
  nestClosOK? cap slots head ≡ true →
  descW gasBig head root 0 0 sched₀ st₀ ≤ W →
  pushValsAdmOK cap slots (proj₁ res)

WidStmt : Set
WidStmt =
  Sched.slots sched₀ ≡ slots →
  nestCapsOK? cap sched₀ st₀ ≡ true →
  nestValOK? cap (obs natᵗ) head ≡ true →
  nestClosOK? cap slots head ≡ true →
  descW gasBig head root 0 0 sched₀ st₀ ≤ W →
  pushValsWidOK cap slots (proj₁ res)

adm-absurd : AdmStmt → ⊥
adm-absurd h with h refl refl refl refl ≤-refl
... | () , _

wid-absurd : WidStmt → ⊥
wid-absurd h with h refl refl refl refl ≤-refl
... | () , _

-- THE FIGURES: the cap the head satisfies against the sizes of the
-- values the body actually emits, so the reading is a crossing and not
-- a scale error
sizes : Stream Γ₂ (obs natᵗ) → List ℕ
sizes [] = []
sizes (em ∷ ems) =
  map (syncSizeᵛ (obs natᵗ)) (proj₁ (splitEvents {A = ℕ} (InstEmit.events em)))
  ++ sizes ems

figs-map : ℕ × List ℕ
figs-map = Caps.cSize cap , sizes (proj₁ res)

figs-map≡ : figs-map ≡ (21 , 25 ∷ [])
figs-map≡ = refl

-- AND IT IS STILL FALSE AT AN EMPTY REGISTRY FIELD, which is what
-- decides where the arrival cap's LEVEL may come from.  The repair the
-- crossing above forces is to read the arrivals one caps level up, and
-- the tempting source for that level is the descent's own delivery
-- count, which the walk statements already bound their level by.  It
-- cannot be: the count is only known to be positive where the cap
-- grants a registration, so at an empty registry field a level bounded
-- by the count alone is level ZERO -- and `frameStep 0` is the
-- identity, so the stepped statement is the flat one, which this
-- witness reaches unchanged.  Same program, same premises, registry
-- emptied.  So the level a `*All` arm reports carries the head's own
-- written size as a SEPARATE summand rather than folded into the
-- count, and the positivity is paid at the one consumer that finally
-- collapses the existential.
capZ : Caps
capZ = caps (syncSizeᵛ (obs natᵗ) head) 99 0

prems-z : Bool × Bool × Bool
prems-z = nestCapsOK? capZ sched₀ st₀
    , nestValOK? capZ (obs natᵗ) head
    , nestClosOK? capZ slots head

prems-z≡ : prems-z ≡ (true , true , true)
prems-z≡ = refl

AdmStmtZ : Set
AdmStmtZ =
  Sched.slots sched₀ ≡ slots →
  nestCapsOK? capZ sched₀ st₀ ≡ true →
  nestValOK? capZ (obs natᵗ) head ≡ true →
  nestClosOK? capZ slots head ≡ true →
  descW gasBig head root 0 0 sched₀ st₀ ≤ W →
  pushValsAdmOK capZ slots (proj₁ res)

WidStmtZ : Set
WidStmtZ =
  Sched.slots sched₀ ≡ slots →
  nestCapsOK? capZ sched₀ st₀ ≡ true →
  nestValOK? capZ (obs natᵗ) head ≡ true →
  nestClosOK? capZ slots head ≡ true →
  descW gasBig head root 0 0 sched₀ st₀ ≤ W →
  pushValsWidOK capZ slots (proj₁ res)

adm-absurd-z : AdmStmtZ → ⊥
adm-absurd-z h with h refl refl refl refl ≤-refl
... | () , _

wid-absurd-z : WidStmtZ → ⊥
wid-absurd-z h with h refl refl refl refl ≤-refl
... | () , _

-- the registry field the two caps differ in, read rather than assumed
regs : ℕ × ℕ
regs = Caps.cReg cap , Caps.cReg capZ

regs≡ : regs ≡ (99 , 0)
regs≡ = refl
