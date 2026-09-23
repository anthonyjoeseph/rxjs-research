-- WHAT A WRITE AT A FRESH IDENTIFIER LEAVES ALONE.  A frame's
-- continuation stands on the store holding what it closed over, and a
-- write to another identifier is the one thing a step may do to the
-- table without moving it.  The bound is a FLOOR taken as an argument
-- rather than read off the mint, so the fact is one family and the
-- counter's monotonicity is re-established separately, where a premise
-- ran at an advanced mint.
--
-- DEAD ROUTE: proving preservation over the SUBSCRIBE RELATION -- "a
--   subscription never writes below the counter it began at".  The
--   connect makes it false: a frame over a share registers the caller's
--   own continuation and folds the definition's synchronous values back
--   down it, so the caller's own node is written at an identifier
--   minted before the subscription began.  Preservation is carried by
--   each ANSWER instead (`Rx.Evaluator.Reducible`'s ground), and the
--   connect answers that the room fell.
-- RECOVERY: git show 33078215:agda/src/Rx/Evaluator/Freshness.agda
--   holds `lookup-set`, `FrameAbove`, `pres-same` and `pres-trans`,
--   which the frame arms spend; the two relation-level families beside
--   it are the dead route above.
module Rx.Evaluator.Freshness where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Decide using (≡ᵇ→≡; ≡ᵇ-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Mint using (nodeᵏ; freshId)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; lookupNode; setNode)

-- where the node counter sits, named once
nodeCt : ∀ {n} {Γ : Ctx n} → Sched Γ → ℕ
nodeCt sched = freshId nodeᵏ (Sched.mint sched)

-- EVERY NODE STRICTLY BELOW THE FLOOR READS BACK EXACTLY AS IT DID.  A
-- record rather than the function it wraps, because both states appear
-- in that type only under a projection, and a transparent alias would
-- leave every composition asking Agda to invert `EvalSt.nodes`.
record PreservedBelow {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                      (f : ℕ) (st st′ : EvalSt e) : Set where
  constructor pres
  field below : ∀ k → k < f
              → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st)

open PreservedBelow public using (below)

-- the written node reads back as written
lookup-set : ∀ {n} {Γ : Ctx n} (nid : NodeId) (ns : NodeState Γ)
             (ts : List (NodeId × NodeState Γ))
           → lookupNode nid (setNode nid ns ts) ≡ just ns
lookup-set nid ns []             rewrite ≡ᵇ-refl nid = refl
lookup-set nid ns ((k , s) ∷ r) with k ≡ᵇ nid in eq
... | true  rewrite ≡ᵇ-refl nid = refl
... | false rewrite eq = lookup-set nid ns r

-- every node other than the written one reads back as it did.  The
-- table is an association list, so the two clauses are the two ways a
-- write can miss: past the end, where the write lands as a fresh head
-- the reader walks past, and at a row whose key is the written one,
-- where the reader's own test already answered.
set-above : ∀ {n} {Γ : Ctx n} (nid k : NodeId) (ns : NodeState Γ)
              (ts : List (NodeId × NodeState Γ))
          → (nid ≡ᵇ k) ≡ false
          → lookupNode k (setNode nid ns ts) ≡ lookupNode k ts
set-above nid k ns []            ne rewrite ne = refl
set-above nid k ns ((j , s) ∷ r) ne with j ≡ᵇ nid in eq
... | true  rewrite ≡ᵇ→≡ j nid eq | ne = refl
... | false with j ≡ᵇ k
...   | true  = refl
...   | false = set-above nid k ns r ne

-- a key below a bound is not that bound
<→≢ᵇ : ∀ {k m} → k < m → (m ≡ᵇ k) ≡ false
<→≢ᵇ {zero}  {suc m} _       = refl
<→≢ᵇ {suc k} {suc m} (s≤s p) = <→≢ᵇ p

-- a write at or above the floor preserves everything below it.  Stated
-- over an equation on the table rather than the states, because a step
-- that leaves the table alone rarely leaves the state alone.
pres-write : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f nid}
               (st st′ : EvalSt e) (ns : NodeState Γ)
             → EvalSt.nodes st′ ≡ setNode nid ns (EvalSt.nodes st)
             → f ≤ nid
             → PreservedBelow f st st′
pres-write {nid = nid} st st′ ns eq f≤nid =
  pres λ k k<f → trans (cong (lookupNode k) eq)
                       (set-above nid k ns (EvalSt.nodes st)
                         (<→≢ᵇ (≤-trans k<f f≤nid)))
