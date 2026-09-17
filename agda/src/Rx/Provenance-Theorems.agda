module Rx.Provenance-Theorems where

open import Data.List                            using (List; map; upTo)
open import Data.List.Membership.Propositional    using (_∈_)
open import Data.List.Relation.Unary.All          using (All)
open import Data.Nat                              using (suc)

open import Rx.Prim      using (Fuel; Id; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Stream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Slots using (Slots)

------------------------------------------------------------------
-- Id discipline: the bridge premise.  formal-verification says the
-- partition matches the ids; THIS says the ids mean provenance.
------------------------------------------------------------------

-- ordinary list inclusion on Id, spelled out over stdlib membership
-- rather than hand-rolled
_⊆ᵢ_ : List Id → List Id → Set
xs ⊆ᵢ ys = All (λ x → x ∈ ys) xs

-- every id an emit carries, in stream order
ids : ∀ {n} {Γ : Ctx n} {t} → Stream Γ t → List Id
ids = map InstEmit.instant

-- {0 … fuel}: Fuel is ℕ (Rx.Prim) and Id is ℕ too (Rx.Prim),
-- so the horizon is the literal enumeration — 0 is the subscribe
-- frame's instant, 1 … fuel the drain counter's (Rx.Evaluator.evaluate,
-- Rx.Evaluator.drain: nextId starts at 1 and increments once per
-- arrival, fuel arrivals at most)
horizon : Fuel → List Id
horizon fuel = upTo (suc fuel)

-- WHAT THIS SAYS, AND WHAT THE NAME SUGGESTS IT SAYS.  The statement is
-- CONTAINMENT and nothing more: every id an emit carries lies inside the
-- horizon.  A singleton is a sublist of the horizon exactly as readily as
-- an enumeration of it, so a machine that minted ONE instant and stamped
-- the entire stream with it satisfies this in full.  Total id collapse is
-- a model of it.
--
-- SEPARATION IS A DIFFERENT CLAIM, AND IT IS NOT THIS MODULE'S.  It is
-- what reconciles a CLAIRVOYANT spec with a STREAMING impl: `Spec` gathers
-- every emit of an instant from anywhere in the stream, while
-- `Implementation` keeps one open batch and flushes on an instant change,
-- so the two agree exactly when an instant's emits are CONTIGUOUS -- once
-- left, never recurring.  That is stated, as `Rx.Protocol`'s freshness
-- clause: `ProtocolSt` carries a watermark and a new instant is admitted
-- only at or above it.  The run's satisfaction of it is the
-- well-formedness face, where `Sound` denominates it per segment and
-- `sound-drain` composes the segments -- proven -- leaving it open at
-- exactly two leaves, `sound-cascade` and `sound-subscribe`.
--
-- SO THE FINDING HERE IS PLACEMENT, NOT A MISSING FACT.  This module's
-- banner says it is where the ids MEAN provenance, and separation is the
-- whole of that meaning; the one statement it carries is containment, and
-- the meaning is established two faces away.  A reader who comes here for
-- the id discipline finds the weaker half and no pointer to the stronger.
-- PROBED: no refutation for `id-inheritance`, with the fuel-3 row checking
--   (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ⊆ᵢ horizon 3.  A confidence receipt over small
--   horizons, not a theorem.  The probe is spent and deleted;
--   `git show 1f1730e^:agda/probe/Battery-Eval-Laws.agda` recovers its rows.
-- PROBED: `Probed.Pipeline-Claims` re-instantiates it against the
--   evaluator as it now reads, at a scripted hot slot under a mapping
--   former, with the witness naming ids 0 and 1 against `horizon 1` --
--   TIGHT, since the last id sits exactly at the fuel bound and one
--   more arrival than the horizon admits would refute the row.  Not
--   reached: any program containing a flattener, because `evaluate↓`
--   does not compute through one while `red-thru` stands.
postulate
  -- every id in the output stream is the id of some arrival's cascade;
  -- sync-spawned inners inherit, never mint
  id-inheritance :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    ids (evaluate↓ fuel e ins) ⊆ᵢ horizon fuel
