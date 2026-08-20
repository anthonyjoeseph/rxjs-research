------------------------------------------------------------------
-- THE NODE TABLE'S TWO REDUCTION FACTS, and one arithmetic fact they
-- need.
--
-- `stepFrame`'s scan-f and take-f clauses INSTALL a node and then READ
-- it back inside the same subscription, so any proof about either has
-- to make `lookupNode nid (setNode nid s …)` and the type-match `w ≟ᵗ
-- u` reduce.  Neither reduces on its own: `setNode` walks the assoc
-- list, and `_≟ᵗ_` is a decision procedure, not a definitional equality.
--
-- THEY LIVE HERE BECAUSE TWO TREES NEED THEM.  The well-formedness
-- branch has needed them since it first stepped a scan frame; the hop
-- ledger's scan push face (.Hop-Spine-Push) needs the identical pair,
-- and it sits BELOW Verify-Well-Formed, so it cannot import them from
-- there.  Rather than grow a second copy — which `make dup-check` would
-- fail, and rightly — the fact moves down to the lowest module both
-- reach.  `≡ᵇ-refl` travels with them because `lookupNode-setNode` is
-- stated over the same `_≡ᵇ_` the table is keyed by.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Node-Table where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _≡ᵇ_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Exp  using (Ctx; Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_)
open import Rx.Evaluator using (NodeId; NodeState; lookupNode; setNode)

≡ᵇ-refl : ∀ (m : ℕ) → (m ≡ᵇ m) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc m) = ≡ᵇ-refl m

-- decidable type-equality is reflexive on the nose — lets stepFrame's scan-f
-- dispatch (w ≟ᵗ u) reduce when the node was installed at the matching type
≟ᵗ-refl : ∀ (u : Ty) → (u ≟ᵗ u) ≡ yes refl
≟ᵗ-refl unitᵗ    = refl
≟ᵗ-refl boolᵗ    = refl
≟ᵗ-refl natᵗ     = refl
≟ᵗ-refl (a ×ᵗ b) rewrite ≟ᵗ-refl a | ≟ᵗ-refl b = refl
≟ᵗ-refl (a +ᵗ b) rewrite ≟ᵗ-refl a | ≟ᵗ-refl b = refl
≟ᵗ-refl (obs a)  rewrite ≟ᵗ-refl a = refl

-- reading back the node you just wrote: the scan/take clauses install their node
-- then read it inside stepFrame, so this pins the lookup that dispatch depends on
lookupNode-setNode : ∀ {n} {Γ : Ctx n} (nid : NodeId) (s : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  lookupNode nid (setNode nid s nodes) ≡ just s
lookupNode-setNode nid s []             rewrite ≡ᵇ-refl nid = refl
lookupNode-setNode nid s ((k , s′) ∷ r) with k ≡ᵇ nid in keq
... | true  rewrite ≡ᵇ-refl nid = refl
... | false rewrite keq = lookupNode-setNode nid s r

-- reading back a node OTHER than the one just written.  The freshness ring
-- (.Node-Fresh) spends this at every `setNode`: below the watermark the key
-- cannot be the frame's own nid, so the write is invisible there.  Note the
-- ORIENTATION — the table is keyed `entry ≡ᵇ query`, so the hypothesis is
-- `nid ≡ᵇ k`, and getting it the other way round costs a build.
-- `≡ᵇ→≡` and the `≢ᵇ` pair below live HERE, at the bottom of the branch,
-- rather than in .Verify-Well-Formed where they were first needed: the
-- freshness ring (.Node-Fresh) sits beneath that tree and needs the identical
-- facts, and `make dup-check` will not let one fact stand under two names.
-- .Part1 re-exports them, so their ~36 call sites up there are unchanged.
≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

-- a strictly-greater id is not equal — the ring's key inequality, and the
-- held instant's `i ≢ j` in .Part10
≢ᵇ-from-< : ∀ {j i : ℕ} → j ≤ i → (suc i ≡ᵇ j) ≡ false
≢ᵇ-from-< z≤n     = refl
≢ᵇ-from-< (s≤s q) = ≢ᵇ-from-< q

sucle→≢ᵇ : ∀ {j nextId : ℕ} → suc j ≤ nextId → (nextId ≡ᵇ j) ≡ false
sucle→≢ᵇ (s≤s q) = ≢ᵇ-from-< q

lookupNode-setNode-other : ∀ {n} {Γ : Ctx n} (k nid : NodeId) (v : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) → (nid ≡ᵇ k) ≡ false →
  lookupNode k (setNode nid v nodes) ≡ lookupNode k nodes
lookupNode-setNode-other k nid v []            ne rewrite ne = refl
lookupNode-setNode-other k nid v ((j , s) ∷ r) ne with j ≡ᵇ nid in jn
... | true  rewrite ≡ᵇ→≡ j nid jn | ne = refl
... | false with j ≡ᵇ k
...   | true  = refl
...   | false = lookupNode-setNode-other k nid v r ne
