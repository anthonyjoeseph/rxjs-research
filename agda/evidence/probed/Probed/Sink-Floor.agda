-- THE DISPATCH NEST AT ITS DEEPEST, walked one rung at a time.  The
-- counter bounding the share fan-out is seeded at the context size, and
-- the sibling probe exercised that seed where it is slack; these rows
-- stand at the deepest nest a context of four admits and spend the
-- counter on DEPTH alone, which is the axis that can outrun the seed.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- THE FLOOR IS NOT MEASURED HERE, BECAUSE IT IS NOW CARRIED IN A TYPE.
-- A registry row's chain is indexed by the floor its source dictates and
-- a sink constructor demands its own index be at least that floor, so
-- "a chain registered on share i sinks only into a strictly later
-- share" is what the row's type says rather than something a run could
-- fail.  A row asserting it could not have failed and so is not a row.

-- AND INDEX ZERO IS NEVER A DISPATCH TARGET, which is what makes the
-- seed slack by construction rather than by luck.  Asynchrony enters
-- only through `scripted`, so a share's definition is synchronous plus
-- reads of lower slots and emits at SUBSCRIBE, never as an arrival.  A
-- share at index zero reads nothing at all, so nothing can ever deliver
-- into it during a drain, and the nest starts at one or above.  The rows
-- below are where that reading is measured rather than argued.

-- NOT COVERED.  One arrival, one telescope shape, and shares that read
-- their predecessor DIRECTLY — a nest whose rungs carry flatteners or
-- takes would spend frames these rows never build.  Nothing here reaches
-- a cancelled registration, a completing share, or a registry admitting
-- two chains at one source, so the staircase is a reading over a
-- registry that is one chain wide at every rung.
-- TARGET: dispatch-saturates @51e075
module Probed.Sink-Floor where

open import Data.Bool using (false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂; ofᵉ;
  mapᵉ; mergeAllᵉ; input)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Strat-Order using (_≺_)
open import Rx.Evaluator using (Sched; EvalSt; root; rootTri; subscribeE;
  rootWitness; sched-init; st-init; dispatchShare; shareAdmit)
open import Rx.Inputs-Below using (below-ctx)
open import Rx.Evaluator-Theorems using (dispatch-saturates)

open import Probed.Apparatus using (Below; Confirms)

----------------------------------------------------------------------
-- THE TELESCOPE, AT ITS DEEPEST.  Slot zero is scripted because nothing
-- else can produce an arrival; the three above it are shares, each
-- reading the one directly below.  That is the longest chain of
-- dispatches a context of four admits.
----------------------------------------------------------------------

Γ₄ : Ctx 4
Γ₄ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- each rung above the first wraps its read in a flattener: a share whose
-- definition is a BARE `input k` does not register on k, so a telescope
-- built that way has no nest to walk at all — measured, and it is the
-- shape that makes the difference between three rungs and none
lit : Fn Γ₄ [] [] [] natᵗ (obs natᵗ)
lit = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

ins : Slots Γ₄
ins zero                   = scripted (cold [] (after 0 , 9 ∷ []))
ins (suc zero)             = shared (input zero)
ins (suc (suc zero))       =
  shared (mergeAllᵉ nothing (mapᵉ lit (input (suc zero))))
ins (suc (suc (suc zero))) =
  shared (mergeAllᵉ nothing (mapᵉ lit (input (suc (suc zero)))))

prog : Closed Γ₄ natᵗ
prog = mergeAllᵉ nothing (ofᵉ (strmᵗ (input (suc (suc (suc zero)))) ∷ []))

ac₀ : Acc _≺_ (rootTri prog ins)
ac₀ = rootWitness prog ins

sd₀ : Sched Γ₄
sd₀ = proj₁ (proj₂ (subscribeE {lo = 4} ac₀ prog {below-ctx prog} root 0 0
                     (sched-init prog ins) (st-init prog)))

st₀ : EvalSt prog
st₀ = proj₂ (proj₂ (subscribeE {lo = 4} ac₀ prog {below-ctx prog} root 0 0
                     (sched-init prog ins) (st-init prog)))

vals₀ : List ℕ
vals₀ = 7 ∷ []

----------------------------------------------------------------------
-- THE NEST THE DISPATCH ACTUALLY WALKS.  One chain per rung, so the
-- fan-out is one wide and the counter is spent entirely on DEPTH — the
-- axis that can outrun the seed.
----------------------------------------------------------------------

floorAdmits₁-is : length (shareAdmit (suc zero) (EvalSt.registry st₀)) ≡ 1
floorAdmits₁-is = refl                                       -- LOAD-BEARING

floorAdmits₃-is : length (shareAdmit (suc (suc (suc zero)))
                      (EvalSt.registry st₀)) ≡ 1
floorAdmits₃-is = refl                                       -- LOAD-BEARING

emitsAt : ℕ → ℕ
emitsAt g = length (proj₁ (dispatchShare {e = prog} ac₀ g 0 0 (suc zero)
                            vals₀ false sd₀ st₀))

-- the counter is READ, and read all the way down: each extra unit buys
-- one more rung of the nest until the nest runs out.  Without this
-- staircase the saturation rows below would be an equality over a
-- machine that ignores its parameter
one-is   : emitsAt 1 ≡ 1                                -- LOAD-BEARING
one-is   = refl

two-is   : emitsAt 2 ≡ 2                                -- LOAD-BEARING
two-is   = refl

three-is : emitsAt 3 ≡ 3                                -- LOAD-BEARING
three-is = refl

-- and here the staircase STOPS, one below the seed: the nest is three
-- rungs because index zero is scripted and cannot be dispatched into,
-- so the fourth unit the arrival seeds is never spent
four-is  : emitsAt 4 ≡ 3                                -- LOAD-BEARING
four-is  = refl

----------------------------------------------------------------------
-- THE STATEMENT AT ITS OWN POINTS, at the deepest nest rather than at a
-- slack one.  `Below` decides the premise, so a counter under the
-- context size leaves the row unsolvable rather than green.
----------------------------------------------------------------------

floorSatSeed : Confirms (dispatch-saturates {e = prog} ac₀ 4 Below 0 0
                     (suc zero) vals₀ false sd₀ st₀)
floorSatSeed = refl

floorSatAbove : Confirms (dispatch-saturates {e = prog} ac₀ 5 Below 0 0
                      (suc zero) vals₀ false sd₀ st₀)
floorSatAbove = refl

-- and at the MIDDLE rung, whose own nest is two deep: the same statement
-- where the seed has two units of slack rather than one
satMid : Confirms (dispatch-saturates {e = prog} ac₀ 4 Below 0 0
                    (suc (suc zero)) vals₀ false sd₀ st₀)
satMid = refl
