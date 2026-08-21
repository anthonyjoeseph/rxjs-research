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

open import Data.Bool using (true; false)
open import Data.Nat  using (_≡ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp  using (Ctx; Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_)
open import Rx.Evaluator using (NodeId; NodeState; lookupNode; setNode)
open import Decide using (≡ᵇ-refl; ≡ᵇ→≡)

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

-- a strictly-greater id is not equal — the ring's key inequality, and the
-- held instant's `i ≢ j` in .Part10


lookupNode-setNode-other : ∀ {n} {Γ : Ctx n} (k nid : NodeId) (v : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) → (nid ≡ᵇ k) ≡ false →
  lookupNode k (setNode nid v nodes) ≡ lookupNode k nodes
lookupNode-setNode-other k nid v []            ne rewrite ne = refl
lookupNode-setNode-other k nid v ((j , s) ∷ r) ne with j ≡ᵇ nid in jn
... | true  rewrite ≡ᵇ→≡ j nid jn | ne = refl
... | false with j ≡ᵇ k
...   | true  = refl
...   | false = lookupNode-setNode-other k nid v r ne
