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

open import Rx.Exp using (Ctx; Exp; uniqᵗ; mintᵉ; Ren∈; renExp)
open import Rx.SExp using (SExp)
open import Rx.Elaborate using (toPlain)

-- A TREE THE ELABORATION BUILT, up to the two operations that move a
-- tree without touching what it emits.  `mintᵉ` because `elaborate` is
-- `mintᵉ ∘ toPlain` and a closed root arrives already minted; renaming
-- because a subtree written under a `mapᵉ` binder stands in a wider
-- term telescope than the elaboration it carries, which is what an
-- author's `source$.pipe(map(x => inner$))` produces.
data Elabᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Set where
  elab-toPlain : ∀ {n} {Γ₀ : Ctx n} {Δᵍ₀ Δ₀ Θ₀ u} (s : SExp Γ₀ Δᵍ₀ Δ₀ Θ₀ u)
               → Elabᵉ (toPlain s)
  elab-mint    : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) t}
               → Elabᵉ e → Elabᵉ (mintᵉ e)
  elab-ren     : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} {e : Exp Γ Δᵍ Δ Θ t}
                 (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
               → Elabᵉ e → Elabᵉ (renExp ρg ρd ρt e)
