-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN LEAVES THE OWNER'S QUEUE UNREAD, so the claim that the
-- owner's cell park-reading after a drain implies an all-inputs-below
-- on the entry queue is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  After `mergeAllDrain` runs, if the owner's
-- node carries a park-reading at floor `i`, then every term in the
-- entry queue `q` has all its inputs below `i`.
--
-- WHERE IT BREAKS.  The `hasRoom lim act = false` arm of
-- `mergeAllDrain` returns IMMEDIATELY with the state UNCHANGED and the
-- queue as the residue — the drain never reads `q`.  The post-drain
-- node reading is then `parkStrat? i (lookupNode allNid (nodes st₀))`,
-- which reduces to `parkStrat? i nothing = true` when the initial
-- state has no node at `allNid` — the wildcard arm of `parkStrat?`.
-- So the hypothesis is satisfied at ANY entry queue, including one
-- holding a term whose input index is at or above `i`.
--
-- THE WITNESS.  Two-element context; the queue holds a single term
-- `input (fsuc fzero)` whose unique input reference is at index 1.
-- With `i = 1`, `lim = just 0`, `act = 0` the room check fails
-- immediately, the state is returned unchanged, the node table is
-- empty, `parkStrat? 1 nothing = true`, so the hypothesis is `refl`.
-- But `inputsBelowᵉ 1 (input (fsuc fzero)) = 1 <ᵇ 1 = false`, so
-- the conclusion is `false ≡ true` — absurd.
--
-- WHAT THIS CLOSES.  The repair needs the owner's cell to be readable
-- BEFORE the drain, so the reading can be compared across the call
-- rather than read from the post-drain state the floor-check never
-- reached.  The conditioned form — OKB carries the link or a separate
-- hypothesis ties the pre-drain cell — is where the statement lives.
-- ══════════════════════════════════════════════════════════════════
module Refuted.MergeAllDrain-OwnerQueue where

open import Data.Bool   using (true)
open import Data.Empty  using (⊥)
open import Data.Fin    using () renaming (zero to fzero; suc to fsuc)
open import Data.List   using (List; _∷_; [])
open import Data.Maybe  using (Maybe; just)
open import Data.Nat    using (ℕ)
open import Data.Product using (proj₂)
open import Data.Vec    using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (Gas; Id; Tick; g0; cold)
open import Rx.Exp   using (Ctx; Closed; natᵗ; emptyᵉ; input; inputsBelowᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeId; Path; root; sched-init; st-init;
         lookupNode; mergeAllDrain)
open import Data.Bool.ListAction using (all)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (parkStrat?)

----------------------------------------------------------------------
-- THE WITNESS.  Two-slot context; the queue holds `input (fsuc fzero)`
-- whose index (1) is not below the floor (1 <ᵇ 1 = false).
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

e₂ : Closed Γ₂ natᵗ
e₂ = emptyᵉ

sl : Slots Γ₂
sl fzero        = scripted (cold [] [])
sl (fsuc fzero) = scripted (cold [] [])

----------------------------------------------------------------------
-- THE DEFECT: `hasRoom (just 0) 0 = false` so the drain returns the
-- state unchanged; the empty node table gives `lookupNode 0 [] =
-- nothing`; and `parkStrat? 1 nothing = true` by the wildcard arm --
-- the hypothesis is `refl`.  But the conclusion is `false ≡ true`.
----------------------------------------------------------------------

mergeAllDrain-ownerQueue-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
     (i : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
     (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
     (sched : Sched Γ) (st : EvalSt e) →
     parkStrat? i (lookupNode allNid (EvalSt.nodes
       (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
         (mergeAllDrain g allNid κ id now lim act q sched st)))))))) ≡ true →
     all (inputsBelowᵉ i) q ≡ true)
  → ⊥
mergeAllDrain-ownerQueue-absurd h
  with h {e = e₂} 1 g0 0 root 0 0 (just 0) 0
          (input (fsuc fzero) ∷ [])
          (sched-init e₂ sl) (st-init e₂) refl
... | ()
