------------------------------------------------------------------
-- BATCHABLE: run the program, then hand its emits to a SECOND
-- evaluator running nothing but `batchSimultaneousᵖ`; what comes out
-- is the spec's grouping of those same emits by instant.
--
-- IMPARTIAL ABOUT HOW THE BATCHER DECIDES.  Nothing here names the
-- InstEmit protocol or any mark the stream carries: the batcher is
-- held to `spec-batchSimultaneous` over `instExtract` of the emits, and
-- whatever it reads to get there is its own business.  Nor can it lean
-- on the program's own synchrony: the second evaluator sees one emit
-- per tick.
--
-- THE SECOND RUN GOES TO COMPLETION: its fuel is the emit count, and
-- that fuel is one per emit is a fact about the evaluator's drain the
-- statement relies on (Anthony: allowed).
--
-- DATA VALUES ONLY (`isData t`), as `left-to-right` states it: a
-- scripted slot carries data, and an observable value is a closure over
-- the first run's context.
------------------------------------------------------------------
module Batchable.Statement where

open import Data.Bool    using (T; true; false)
open import Data.Fin     using (zero)
open import Data.List    using (List; []; _∷_; map; length; concat)
open import Data.Nat     using (_≟_)
open import Data.Product using (map₂; proj₂)
open import Data.Unit    using (tt)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel; Id; valueᵖ; completeᵖ; after_,_; hot)
open import Rx.Exp       using (Ctx; Ty; Val; isData; input)
open import SExp.Syntax      using (SExp; Kinds; emitᵗ)
open import Rx.Slots     using (Slots; scripted)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.InstEmit  using (machineEmitᵗ)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Plain     using (unplainᵈ)
open import SExp.Batch     using (batchSimultaneousᵖ)
open import SExp.Pipeline using (emitsᴵ; runᴵ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Batchable.Inst-Extract using (instExtract)
import Spec
open Spec Id _≟_ using (spec-batchSimultaneous)

-- the second evaluator's one input: the emits
Γᴮ : Ty → Ctx 1
Γᴮ t = Vec.[ machineEmitᵗ t ]

emitData : ∀ t → T (isData t) → T (isData (machineEmitᵗ t))
emitData t ok with isData t
emitData t ok | true  = tt
emitData t () | false

-- the first run's emits, moved into the second evaluator's context
emitsᴮ : ∀ {n} {Γ′ : Ctx n} t → T (isData t) → Burst Γ′ (emitᵗ t) → List (Val (Γᴮ t) (machineEmitᵗ t))
emitsᴮ t ok []               = []
emitsᴮ t ok (valueᵖ v ∷ es)  = unplainᵈ (machineEmitᵗ t) (emitData t ok) v ∷ emitsᴮ t ok es
emitsᴮ t ok (completeᵖ ∷ es) = emitsᴮ t ok es

-- the second evaluator: `batchSimultaneousᵖ` over the emits, one per
-- tick, run to completion
batchedᴮ : ∀ t → T (isData t) → List (Val (Γᴮ t) (machineEmitᵗ t)) → List (List (Val (Γᴮ t) t))
batchedᴮ t ok xs =
  map proj₂ (instExtract (decodeEmits (concat (evaluate↓ (length xs) (batchSimultaneousᵖ (input zero)) slots))))
  where
  slots : Slots (Γᴮ t)
  slots zero = scripted {ok = emitData t ok} (hot (map (λ x → after 0 , x) xs))

Batchable : Set
Batchable =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  batchedᴮ t ok (emitsᴮ t ok (emitsᴵ κ fuel e ins))
    ≡ spec-batchSimultaneous (map (map₂ (unplainᵈ t ok)) (instExtract (runᴵ κ fuel e ins)))

postulate
  batchable : Batchable
