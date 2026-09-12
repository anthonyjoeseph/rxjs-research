------------------------------------------------------------------
-- THE ENTRY INVARIANT: the motive both settled peels are stated
-- against.
--
-- The evaluator's guards do not compare a term against its own
-- measure; they compare it against the TRIPLE THE WITNESS STANDS AT,
-- which is a separate quantity the machine seeds and re-seeds.  So a
-- peel lemma cannot be a fact about syntax alone — it needs to know
-- how the triple relates to the term about to be subscribed, and that
-- relation is what this module names.
--
-- IT IS A PAIR OF INEQUALITIES AND NOT A PAIR OF EQUATIONS, and the
-- two components are loose for DIFFERENT reasons.  The sync component
-- is re-seeded only where a μ peels, while `subscribeE` steps into an
-- operator's argument carrying the SAME witness — so by the time the
-- walk reaches a `μᵉ`, the component is the reading of some ENCLOSING
-- term and the subterm's own reading is under it.  The unconnected
-- count is re-seeded only AT a connect, while the connected list grows
-- at every connect anywhere beneath — so a caller returning from a
-- nested latch holds a count that is STALE and too large.  Never too
-- small, because nothing un-latches; that asymmetry is what makes one
-- inequality the whole of what either peel needs.
--
-- THE RANK COMPONENT IS ABSENT HERE ON PURPOSE.  An emitted inner is a
-- runtime value structurally unrelated to the term its emitter was
-- subscribing, so no reading of the term bounds it and no conjunct
-- stated over syntax could carry it.  That reading travels as a
-- strengthened return type on the burst-producing functions instead,
-- which is why this motive stops at two.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Entry where

open import Data.List using (List; [])
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri)
open import Rx.Evaluator using (unconn; rootTri)

-- the triple the machine stands at READS the term it is about to
-- subscribe: the unconnected count bounds the first component and the
-- sync size the third.  The rank component is unconstrained here.
EntryReads : ∀ {n} {Γ : Ctx n} {u} → Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads (U , _ , s) o sl cs = unconn sl cs ≤ U × syncSizeᵉ o ≤ s

-- the root seeds both components at the term's own reading, so the
-- invariant holds there by reflexivity — the one place the seeding has
-- to be shown adequate
rootTri-reads : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  EntryReads (rootTri e ins) e ins []
rootTri-reads e ins = ≤-refl , ≤-refl
