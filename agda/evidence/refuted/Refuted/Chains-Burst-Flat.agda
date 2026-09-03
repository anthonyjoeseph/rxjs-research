-- ══════════════════════════════════════════════════════════════════
-- THE CASCADE'S BURST BOUND IS FALSE AT A FLAT WIDTH, because two
-- consecutive `*All` frames MULTIPLY a burst and the entry width is
-- one number read once.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAYS.  Every chain an arrival drives keeps every
-- hop's value list under ONE width -- the entry cap's, plus one -- from
-- the arrival's own payload down to the root, given only that the
-- state fits the entry cap.  The width is flat: the same `W` is asked
-- of the values a frame takes and of the values it hands on.
--
-- WHERE IT BREAKS.  A `thru-outer` frame subscribes EACH value it is
-- handed and concatenates what the inners emit, so a burst of `w`
-- observables each `w` wide comes out as `w²` values -- and `w²`
-- exceeds `w + 1` from two upward.  The witness is a scripted nat
-- whose map wraps it as two inner observables of two values each: one
-- value at the map, two at the first `mergeAll`, four at the root,
-- against a cap of width two granting three.  The state is the
-- evaluator's own after the root subscribe, the arrival is the one its
-- scheduler pops, and the chain is the registry's -- nothing is
-- hand-built.
--
-- AND CONDITIONING ON THE ARRIVAL DOES NOT REPAIR IT.  The arrival is
-- a nat, so it fits every cap; the widening happens to a value the MAP
-- built, whose own width is exactly the cap's.  So the crossing is not
-- an oversized payload -- it is the dynamics of two `*All` layers, the
-- same multiplication the walk face prices by STEPPING its level once
-- per frame.  A flat width cannot state it whatever it is conditioned
-- on; only a level-indexed one can, which makes this the burst
-- currency's copy of `Refuted.Chain-Step-Flat`.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about a bound at the EXIT
-- width, which is what the statement's own header argues for and
-- which `w²` sits under; whether the store face can afford that
-- denomination is arithmetic against the exit size, not a question
-- this witness answers.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chains-Burst-Flat where

open import Data.Bool using (Bool; true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; after_,_; cold)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; emptyᵉ; mapᵉ; mergeAllᵉ; input;
         nat̂; strmᵗ; applyFn)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator
  using (root; sched-init; st-init; subscribeE; budgetAt; EvalSt; Sched;
         Stream; Arrival; LiveSource; schedGo; arrVal; arrTy; arrTick;
         chainsOf; cascadeLatch; Path; _↠_; map-f; thru-outer; mergeAllᵒ;
         stepFrame)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK
  using (chainsBurstOK)
open import Refuted.Demand-Programs using (Γ₂)

-- one scripted nat, arriving at the subscription tick; the shared slot
-- is empty so the budget's syntax count stays small
slots : Slots Γ₂
slots fzero        = shared emptyᵉ
slots (fsuc fzero) = scripted (cold [] ((after 0 , 0) ∷ []))

-- the step function: a nat in, two inner observables of two values out
-- -- width two at both layers, which is the cap's own width
wide : Fn Γ₂ [] [] [] natᵗ (obs (obs natᵗ))
wide = strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ []))
                 ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ []))

head : Closed Γ₂ natᵗ
head = mergeAllᵉ nothing (mergeAllᵉ nothing (mapᵉ wide (input (fsuc fzero))))

-- SIZE AND REGISTRY GENEROUS, WIDTH AT WHAT THE MAP BUILDS: the map's
-- value is admitted at this width by construction, so what is left is
-- the multiplication and not an oversized value
cap : Caps
cap = caps 256 2 1

-- THE STATEMENT'S OWN FUEL, so the rows run the walk the chain
-- predicate runs and not a stand-in
gas : Gas
gas = budgetAt head slots 0

R : Stream Γ₂ natᵗ × Sched Γ₂ × EvalSt head
R = subscribeE gas head root 0 0 (sched-init head slots) (st-init head)

sched₁ : Sched Γ₂
sched₁ = proj₁ (proj₂ R)

st₁ : EvalSt head
st₁ = proj₂ (proj₂ R)

-- THE ARRIVAL IS THE ONE THE SCHEDULER POPS.  The fallback arm below is
-- never taken -- `reached` pins the pop to the popped pair by `refl`,
-- which the fallback could not satisfy.
popped : Arrival Γ₂ × List (LiveSource Γ₂)
popped with schedGo (Sched.live sched₁)
... | inj₂ p = p
... | inj₁ _ = record { tick = 0 ; ordinal = 0 ; source = 0 ; elemTy = natᵗ
                      ; payload = 0 ; isLast = true } , []

a : Arrival Γ₂
a = proj₁ popped

reached : schedGo (Sched.live sched₁) ≡ inj₂ popped
reached = refl

-- THE CHAIN IS THE REGISTRY'S: the map, the inner `mergeAll`, the outer
path : Path Γ₂ natᵗ natᵗ
path = map-f wide ↠ (thru-outer mergeAllᵒ 1 ↠ (thru-outer mergeAllᵒ 0 ↠ root))

chain≡ : chainsOf a st₁ ≡ (0 , path) ∷ []
chain≡ = refl

-- the premises, pinned true where the row runs rather than assumed
prems : Bool × Bool
prems = capsOK? cap sched₁ st₁
      , valCaps? cap slots (arrTy a) (arrVal a)

prems≡ : prems ≡ (true , true)
prems≡ = refl

Stmt : Set
Stmt =
  Sched.slots sched₁ ≡ slots →
  capsOK? cap sched₁ st₁ ≡ true →
  valCaps? cap slots (arrTy a) (arrVal a) ≡ true →
  chainsBurstOK (suc (Caps.cWid cap)) a 1 (chainsOf a st₁) sched₁
                (cascadeLatch a st₁)

-- the root conjunct of the one chain: four values against three
chains-burst-flat-absurd : Stmt → ⊥
chains-burst-flat-absurd h =
  ≤⇒≤ᵇ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ (h refl refl refl))))))))

-- THE FIGURES, spelled out so a repair that moves any of them fails
-- here naming the number: the width the map's value reads at the
-- table, the width the cap grants, and the burst at each hop -- one at
-- the map, one out of it, two out of the inner `mergeAll`, four at
-- the root.
built : Val Γ₂ (obs (obs natᵗ))
built = applyFn wide (arrVal a)

widths : ℕ × ℕ
widths = pWᵛ 2 slots (obs (obs natᵗ)) built , Caps.cWid cap

widths≡ : widths ≡ (2 , 2)
widths≡ = refl

st′ : EvalSt head
st′ = record (cascadeLatch a st₁)
        { delivered = 0 ∷ EvalSt.delivered (cascadeLatch a st₁) }

vals₀ : List (Val Γ₂ natᵗ)
vals₀ = arrVal a ∷ []

step₁ = stepFrame gas 1 (arrTick a) (map-f wide)
          (thru-outer mergeAllᵒ 1 ↠ (thru-outer mergeAllᵒ 0 ↠ root))
          vals₀ (Arrival.isLast a) sched₁ st′

step₂ = stepFrame gas 1 (arrTick a) (thru-outer mergeAllᵒ 1)
          (thru-outer mergeAllᵒ 0 ↠ root)
          (proj₁ step₁) (proj₁ (proj₂ (proj₂ step₁)))
          (proj₁ (proj₂ (proj₂ (proj₂ step₁))))
          (proj₂ (proj₂ (proj₂ (proj₂ step₁))))

step₃ = stepFrame gas 1 (arrTick a) (thru-outer mergeAllᵒ 0) root
          (proj₁ step₂) (proj₁ (proj₂ (proj₂ step₂)))
          (proj₁ (proj₂ (proj₂ (proj₂ step₂))))
          (proj₂ (proj₂ (proj₂ (proj₂ step₂))))

hops : ℕ × ℕ × ℕ × ℕ
hops = length vals₀ , length (proj₁ step₁) , length (proj₁ step₂)
     , length (proj₁ step₃)

hops≡ : hops ≡ (1 , 1 , 2 , 4)
hops≡ = refl
