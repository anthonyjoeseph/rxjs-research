------------------------------------------------------------------
-- LEFT-TO-RIGHT: run the program with `batchSimultaneousᵖ` on the end,
-- read each emit's values, and join the batches back up -- that is the
-- values the program read as plain rxjs delivers, in order.
--
-- AT ONE MORE UNIT OF FUEL, BECAUSE A BATCH CANNOT LEAVE BEFORE ITS
-- INSTANT IS SEEN TO END.  What says so is the next instant's first
-- emit or the run's completion, so a run the fuel cuts off holds its
-- last instant's values that the plain run, cut at the same point, has
-- already delivered.  So the joined run at a fuel is a PREFIX of the
-- plain run, and the plain run a prefix of the joined one a single
-- arrival later: never ahead of rxjs, and never more than one arrival
-- behind (Anthony).
--
-- CLOSES A CHEAT THE OTHER TOP-LINE STATEMENTS LEAVE OPEN.
-- Elaborating every program to `empty` is trivially batched, and fails
-- left-to-right.
--
-- AT DATA TYPES ONLY, AND THAT IS A LIMIT OF WHAT `≡` CAN SAY RATHER
-- THAN OF THE CLAIM.  The two runs stand in different contexts -- the
-- elaboration's reads a share at the InstEmit -- and a value at `obs`
-- is a closure over its context, so two of them are not comparable by
-- equality at all.  A data value is the same value in every context,
-- which `unplainᵈ` says.
--
-- OVER EVERY PROGRAM, SO OVER EVERY TIMED ONE: at `timed κ e` the
-- values compared are (packet, value) pairs, and the batches are then
-- read against the packets.
--
-- TWO CLAIMS, AND THE BODY KEEPS THEM APART.  That the elaborated run's
-- values ARE the plain run's is `simulation`'s; that the batcher only
-- delays them, by at most one arrival, is `batched-sandwich`'s, stated
-- against the elaborated run itself, which is the only run the batcher
-- sees.
------------------------------------------------------------------
module Left-To-Right.Statement where

open import Data.Bool    using (T)
open import Data.List    using (List; []; concat; map)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Nat     using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx; Val; isData)
open import SExp.Syntax      using (SExp; Kinds; plainᵏ)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Plain     using (unplainᵈ)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.InstEmit.Decode using (decodeEmits)
open import SExp.Batch     using (batchSimultaneousᵖ)
open import SExp.Pipeline using (elaborateImpl; embedSlotsImpl; runᴵ; runᴾ)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Statement using (simulation; agrees-values)

-- the batches, joined back up
joinedᴵ : ∀ {n} {Γ : Ctx n} {t} → T (isData t) → (κ : Kinds n) → Fuel
        → SExp Γ [] [] [] t → SimulSlots Γ κ → List (Val Γ t)
joinedᴵ {t = t} ok κ fuel e ins =
  map (unplainᵈ t ok) (concat (map proj₂ (instExtract (decodeEmits
      (concat (evaluate↓ fuel (batchSimultaneousᵖ (elaborateImpl κ e)) (embedSlotsImpl ins)))))))

-- the elaborated run without the batcher, read at data
valsᴵ : ∀ {n} {Γ : Ctx n} {t} → T (isData t) → (κ : Kinds n) → Fuel
      → SExp Γ [] [] [] t → SimulSlots Γ κ → List (Val Γ t)
valsᴵ {t = t} ok κ fuel e ins = map (unplainᵈ t ok) (map proj₂ (instExtract (runᴵ κ fuel e ins)))

Left-To-Right : Set
Left-To-Right =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Prefix _≡_ (joinedᴵ ok κ fuel e ins) (runᴾ fuel e ins) ×
  Prefix _≡_ (runᴾ fuel e ins) (joinedᴵ ok κ (suc fuel) e ins)

-- the batcher's own sandwich, against the run it batches
Batched-Sandwich : Set
Batched-Sandwich =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Prefix _≡_ (joinedᴵ ok κ fuel e ins) (valsᴵ ok κ fuel e ins) ×
  Prefix _≡_ (valsᴵ ok κ fuel e ins) (joinedᴵ ok κ (suc fuel) e ins)

postulate
  -- PROBED: `Probed.Left-To-Right` -- both prefixes decided at fuel 30
  --   over the same three first-order programs.  Every run completes
  --   inside its fuel, so the one-past slack is not exercised.
  batched-sandwich : Batched-Sandwich

left-to-right : Left-To-Right
left-to-right {Γ = Γ} {t = t} ok κ fuel e ins =
  subst (Prefix _≡_ (joinedᴵ ok κ fuel e ins)) same (proj₁ sandwich) ,
  subst (λ xs → Prefix _≡_ xs (joinedᴵ ok κ (suc fuel) e ins)) same (proj₂ sandwich)
  where
    sandwich = batched-sandwich ok κ fuel e ins
    same : valsᴵ ok κ fuel e ins ≡ runᴾ fuel e ins
    same = agrees-values (plainᵏ Γ κ) Γ t ok (proj₁ (simulation κ fuel e ins))
