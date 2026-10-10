------------------------------------------------------------------
-- LEFT-TO-RIGHT: run the program with `batchSimultaneousᵖ` on the end,
-- read each emit's values, and join the batches back up -- that is the
-- values the program read as plain rxjs delivers, in order.
--
-- AT ONE MORE UNIT OF FUEL, BECAUSE A BATCH CANNOT LEAVE BEFORE ITS
-- INSTANT IS SEEN TO END.  What says so is the next instant's first
-- emit or the run's completion, so a run the fuel cuts off holds its
-- last instant's values that the plain run, cut at the matching point,
-- has already delivered.  So the joined run at a fuel is a PREFIX of the
-- plain run, and the plain run a prefix of the joined one a single impl
-- arrival later: never ahead of rxjs, and never more than one arrival
-- behind (Anthony).
--
-- THE IMPL RUNS AT ITS OWN FUEL, NEVER LESS THAN THE PLAIN RUN'S
-- (Anthony).  The fuel that matches is the batcher's own, never less
-- than `simulation`'s.
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
open import Data.List    using ([])
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Nat     using (suc; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx; isData)
open import SExp.Syntax      using (SExp; Kinds; plainᵏ)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.Pipeline using (runᴾ)
open import Simulation.Statement using (simulation; agrees-values)
open import SExp.Readings using (joinedᴵ; valsᴵ)


Left-To-Right : Set
Left-To-Right =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ Fuel λ fuelᴵ → fuel ≤ fuelᴵ ×
  Prefix _≡_ (joinedᴵ ok κ fuelᴵ e ins) (runᴾ fuel e ins) ×
  Prefix _≡_ (runᴾ fuel e ins) (joinedᴵ ok κ (suc fuelᴵ) e ins)

-- the batcher's own sandwich, against the run it batches, at a fuel of
-- the batcher's own
Batched-Sandwich : Set
Batched-Sandwich =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ Fuel λ fuelᴮ → fuel ≤ fuelᴮ ×
  Prefix _≡_ (joinedᴵ ok κ fuelᴮ e ins) (valsᴵ ok κ fuel e ins) ×
  Prefix _≡_ (valsᴵ ok κ fuel e ins) (joinedᴵ ok κ (suc fuelᴮ) e ins)

postulate
  -- THE BATCHER'S FUEL IS ITS OWN, BECAUSE A UNIT OF FUEL IS AN ARRIVAL
  -- AND AN ARRIVAL CAN BE SILENT.  A batch leaves only when the next
  -- instant's first emit or the run's completion closes its instant,
  -- and the arrival one unit past the run's fuel may put nothing on the
  -- run at all, so the batcher can need several units past it.  The
  -- witness is the fuel just before the arrival that closes the open
  -- instant -- not past it, or the joined run overtakes the run it was
  -- read against.
  --
  -- REFUTED: `Refuted.Batched-Sandwich`, read with
  --   `git show c2e60cb8:agda/evidence/refuted/Refuted/Batched-Sandwich.agda`
  --   -- the slack fixed at one unit
  --   past the run's own fuel, false at fuel one where the second
  --   arrival is silent.
  batched-sandwich : Batched-Sandwich

left-to-right : Left-To-Right
left-to-right {Γ = Γ} {t = t} ok κ fuel e ins =
  proj₁ sandwich , ≤-trans (proj₁ (proj₂ sim)) (proj₁ (proj₂ sandwich)) ,
  subst (Prefix _≡_ (joinedᴵ ok κ (proj₁ sandwich) e ins)) same (proj₁ (proj₂ (proj₂ sandwich))) ,
  subst (λ xs → Prefix _≡_ xs (joinedᴵ ok κ (suc (proj₁ sandwich)) e ins)) same (proj₂ (proj₂ (proj₂ sandwich)))
  where
    sim = simulation κ fuel e ins
    fuelᴵ = proj₁ sim
    sandwich = batched-sandwich ok κ fuelᴵ e ins
    same : valsᴵ ok κ fuelᴵ e ins ≡ runᴾ fuel e ins
    same = agrees-values (plainᵏ Γ κ) Γ t ok (proj₁ (proj₂ (proj₂ sim)))
