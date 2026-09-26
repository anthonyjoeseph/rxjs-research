-- WHICH ROOTS A RUN THEOREM QUANTIFIES OVER: the trees the elaboration
-- built, stated as a predicate on the plain tree.
--
-- THE HOLE THIS CLOSES, AND IT IS AT THE ROOT ALONE.  A run theorem
-- phrased over an ARBITRARY `Closed Γ t` is false, and Refuted.
-- Forged-Root exhibits the counterexample: the root
--
--   mintᵉ (ofᵉ (instEmitᵛ nilᵗ (varᵗ (here refl)) (varᵗ (here refl))
--                deliveryᵛ ∷ []))
--
-- drives the protocol automaton to `nothing` -- a `delivery` whose
-- source no `init` ever enlisted -- over a slot table that is beyond
-- reproach.  Nothing about the TABLE is at fault there, so no condition
-- on slots can answer it; the root has to be one the elaboration
-- produced.
--
-- WHY THIS IS THE WHOLE OF IT, where a predicate mirroring the grammar
-- clause by clause was once needed.  That larger family existed to
-- police what a SHARED DEFINITION could emit, because `subs-shared`
-- subscribes a definition straight down the consumer's path.  `Rx.
-- Slots` now bars the definition types that could exploit it outright
-- (`isData`), so the definition side is closed by the telescope and
-- what remains is this: the root is an elaboration.  Being one former
-- deep rather than a whole second grammar, the induction over a run
-- stays single-layer.
module Rx.Elaborated where

open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Rx.Exp using (Ctx; Exp; uniqᵗ; mintᵉ; Ren∈; renExp)
open import Rx.SExp using (SExp; Kinds; plainᵏ)
open import Rx.Simul-Slots using (SimulSlots)
open import Implementation.Pipeline using (embedSlotsImpl)
open import Rx.Slots using (Slots)
open import Rx.Elaborate using (toEnvelope)

-- A TREE THE ELABORATION BUILT, up to the two operations that move a
-- tree without touching what it emits.  `mintᵉ` because `elaborateImpl` is
-- `mintᵉ ∘ toEnvelope` and a closed root arrives already minted; renaming
-- because a subtree written under a `mapᵉ` binder stands in a wider
-- term telescope than the elaboration it carries, which is what an
-- author's `source$.pipe(map(x => inner$))` produces.
data Elabᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Set where
  elab-toEnvelope : ∀ {n} {Γ₀ : Ctx n} (κ : Kinds n) {Δᵍ₀ Δ₀ Θ₀ u}
                 (s : SExp Γ₀ Δᵍ₀ Δ₀ Θ₀ u)
               → Elabᵉ (toEnvelope κ s)
  elab-mint    : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) t}
               → Elabᵉ e → Elabᵉ (mintᵉ e)
  elab-ren     : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} {e : Exp Γ Δᵍ Δ Θ t}
                 (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
               → Elabᵉ e → Elabᵉ (renExp ρg ρd ρt e)

-- AND THE SAME THING FOR THE SLOT TABLE, for the same reason and at
-- the same depth.  `Elabᵉ` says the ROOT was elaborated; that alone
-- was enough only while `Rx.Slots` barred observable-typed shared
-- defs, and that bar is gone -- a plain shared def at `obs (emitᵗ u)`
-- emits observables the consumer's `mergeAllˢ` subscribes past
-- `stamp`, which is the forgery channel in the table.  `Rx.Simul-Slots`
-- shuts it by construction rather than by side condition, so what a
-- leaf needs to know is that the table CAME from there.
--
-- ONE FORMER, like `Elabᵉ`: the kinds and the author's telescope are
-- existentially held rather than threaded through the statements, so
-- no leaf is re-indexed and every call site discharges it by naming
-- the table it already had.
-- IT IS A RECORD OVER THE TABLE AS A PARAMETER RATHER THAN A DATATYPE
-- INDEXED BY IT, and that is forced rather than stylistic.  Indexed,
-- `Elabˢ (Sched.slots sched)` makes the premise's index drive the
-- unification of `sched` itself: Agda eta-expands the field selector
-- into a lambda and the schedule can no longer be solved from the
-- cascade derivation it is supposed to come from.  As a parameter
-- nothing is matched on, so the premise constrains only what it says.
record Elabˢ {n} {Γ : Ctx n} (ins : Slots Γ) : Set where
  constructor elab-slots
  field
    {ctx}   : Ctx n          -- the telescope the AUTHOR wrote
    {kinds} : Kinds n        -- and how the elaboration reads each slot
    ctx-eq  : Γ ≡ plainᵏ ctx kinds
    source  : SimulSlots ctx kinds
    embeds  : subst Slots ctx-eq ins ≡ embedSlotsImpl source
