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
open import SExp.Syntax      using (SExp; Kinds; emitᵗ; plainᵗ)
open import Rx.Slots     using (Slots; scripted)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.InstEmit  using (machineEmitᵗ)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Plain     using (unplainᵈ)
open import SExp.Batch     using (batchSimultaneousᵖ)
open import SExp.Pipeline using (emitsᴵ)
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

-- BOTH SIDES ARE FUNCTIONS OF ONE RUN'S EMITS: the second evaluator's
-- batches of them, and the spec's grouping of the same emits decoded
batchedᴱ : ∀ {n} {Γ′ : Ctx n} t → T (isData t) → Burst Γ′ (emitᵗ t) → List (List (Val (Γᴮ t) t))
batchedᴱ t ok es = batchedᴮ t ok (emitsᴮ t ok es)

groupedᴱ : ∀ {n} {Γ′ : Ctx n} t → T (isData t) → Burst Γ′ (emitᵗ t) → List (List (Val (Γᴮ t) t))
groupedᴱ t ok es =
  spec-batchSimultaneous (map (map₂ (unplainᵈ t ok)) (instExtract (decodeEmits {a = plainᵗ t} es)))

Batchable : Set
Batchable =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  batchedᴱ t ok (emitsᴵ κ fuel e ins) ≡ groupedᴱ t ok (emitsᴵ κ fuel e ins)

postulate
  -- Seeds 12..16 at depth 3, fuel one, also gave no red under
  -- `make qc-batchable`.
  -- PROBED: make qc-batchable QC='17 1000 3' QC_FUEL=1
  --   decided by `CLI.QuickCheck`'s `pairᴮ`: 338 cases grouping values
  --   under an author flattener and 89 under a `μ`, every one agreeing.
  --   unaimed.
  -- PROBED: `Probed.Batchable` -- by `refl` at fuel 30 over three first-order
  --   programs: a scripted slot taken to one of two arrivals, the script's
  --   two arrivals kept (two instants), and a literal of two values (one
  --   instant).  Not a flattener, a share, a `μ` nor a cold slot: a
  --   flattener's run does not reduce in the typechecker inside 8 GB at fuel
  --   30 or 3, so those shapes are `make quickcheck`'s alone.
  batchable : Batchable
